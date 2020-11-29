// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.

namespace MyBigInteger

open System
open System.Diagnostics.Contracts
open System.Collections.Generic
open System.Globalization
open System.Numerics
open System.Text

type ints = int array
// Taken from fsharp/src/fsharp/FSharp.Core/math/n.fs
// Have n = sum (from i=0 to bound) a.[i] * baseN ^ i
// Have 0 <= a[i] < baseN
// Zero is {bound = 0, a=...}.
type BigNat = {
        mutable sign: int;  // 符号
        mutable len : int;  // 確保した配列の長さ
        mutable used : int; // 実際に使っている長さ
        digits : ints;
    }

module MyFirstBigInt =
    let maxInt a b = if a < b then b else (a:int)
    let minInt a b = if a < b then a else (b:int)
    let baseN = 10000

    // pow32 :: int -> int -> int
    // x^nを返す関数
    let rec pow32 x n =
        match n with
        |   0 -> 1
        |   _ -> match n % 2 with
                 | 0 -> pow32 (x * x) (n / 2)
                 | _ -> x * pow32 (x * x) (n / 2)

    // boundInt :: int
    // Int32.MaxValueのbaseN進数で数えた桁数
    let boundInt =
        let rec iter n i =
            if n > 1 then iter (n / baseN) (i+1) else i
        iter Int32.MaxValue 0


    // 0でない最大の桁のindexを返す
    let findMaxIndex d =
        let rec findMaxIndex_sub (d:ints) i =
            match i with
            | -1 -> 0
            | _ -> match d.[i] with
                   | 0 -> findMaxIndex_sub d (i - 1)
                   | _ -> i + 1
        findMaxIndex_sub d.digits (d.len - 1)


    // BigNatのキャリーオーバー(アンダー)を正規化する関数。
    // 確保された最上位の桁(n.digits.[n.len])のキャリーオーバー(アンダー)は検査しない
    let norm_carry (n:BigNat) =
        let ret_sign = n.sign
        for i in 0 .. (n.len - 2) do
            if n.sign = 1 then
                while n.digits.[i] >= baseN do
                    n.digits.[i] <- n.digits.[i] - baseN
                    n.digits.[i+1] <- n.digits.[i+1] + 1
                while n.digits.[i] < 0 do
                    n.digits.[i] <- n.digits.[i] + baseN
                    n.digits.[i+1] <- n.digits.[i+1] - 1
            else // n.sign = -1
                while n.digits.[i] > 0 do
                    n.digits.[i] <- n.digits.[i] - baseN
                    n.digits.[i+1] <- n.digits.[i+1] + 1
                while n.digits.[i] <= -baseN do
                    n.digits.[i] <- n.digits.[i] + baseN
                    n.digits.[i+1] <- n.digits.[i+1] - 1
                n.digits.[i] <- abs n.digits.[i]

    // normN :: BigNat -> BigNat
    // BigNatの正規化関数
    let normN n =
        do n.used <- findMaxIndex n
        do norm_carry n
        n

    // createZero :: int -> BigNat
    // 値が+0でn桁のBigNatを生成する関数
    let createZero n =
        {sign = 1; len = n; used = 1; digits = Array.zeroCreate n}

    // embed :: int -> BigNat
    // 値がx(>=0)のBigNatを生成する関数。x<0の場合は+0の値を生成する
    let embed x =
        let convToDigits rt x =
            let rx = ref x
            for i in 0 .. (rt.len-1) do
                do rt.digits.[i] <- !rx % baseN
                do rx := !rx / baseN
        let sign = if x >=0 then 1 else -1
        let x = abs x
        let rt = createZero boundInt
        do rt.sign <- sign
        do convToDigits rt x
        do rt.used <- findMaxIndex rt
        rt

    // index :: BigNat -> int -> int
    // xのi桁めの数字を返す関数
    let index x i = if i < x.len then x.digits.[i] else 0

    // babscmp :: BigNat -> BigNat -> int
    // BigNatの比較を行う関数
    let babscmp b1 b2 =
        let cmp n1 n2 i =
            let rec cmp_sub i =
                match i with
                | -1 -> 0
                | _  -> if (n1.digits.[i] > n2.digits.[i]) then 1
                        elif n1.digits.[i] < n2.digits.[i] then -1
                        else cmp_sub (i-1)
            cmp_sub i
        let b1u = findMaxIndex b1
        let b2u = findMaxIndex b2
        if b1u > b2u then 1
        elif b1u < b2u then -1
        else // b1u = b2u
            cmp b1 b2 b1u

    // bshow :: BigNat -> string
    // BigNatをstringに変換する関数
    let bshow (n:BigNat) =
        let sa : string array = Array.zeroCreate n.used
        // 最上位以外は0パディング(baseNが10のべき乗であることが前提)
        for i in 0 .. (n.used - 2) do
            do sa.[i] <- (n.digits.[i] + baseN).ToString().Substring(1)
        // 最上位は0パディングなし
        do sa.[n.used - 1] <- n.digits.[n.used - 1].ToString()
        let sa = Array.rev(sa)
        (if n.sign < 0 then "-" else "" )+ String.Join ("", sa)

    let bcopy p =
        let q = createZero p.len
        for i in 0..(p.len-1) do
            q.digits.[i] <- p.digits.[i]
        do q.used <- findMaxIndex q
        q

    let zero = embed 0
    let one  = embed 1

    // --------------------------------------------------------

    let add p q = 
        let ret_sign = 
            if (p.sign * q.sign) < 0 then 
                let c = babscmp p q
                if c > 0 then p.sign
                elif c < 0 then q.sign
                else 1
            else p.sign
        let sum_len = maxInt p.used q.used + 1
        let sum = createZero sum_len
        do sum.sign <- ret_sign
        for i in 0 .. (sum_len - 1) do
            let x = p.sign * (index p i) + q.sign * (index q i)
            do sum.digits.[i] <- x
        normN sum

    let neg p =
        let q = bcopy p
        match p.sign with
        | 1 -> q.sign <- -1
        | _ -> q.sign <-  1
        q

    let sub p q =
        add p (neg q)

    let rec mulP i n c p q r =
        let rec mulPP j s =
            if j <= i then
                let ss = index p (i-j) * index q j
                mulPP (j+1) (s+ss) 
            else
                s
        if i < n then
            let x = mulPP 0 0 + c
            let d, m = x / baseN, x % baseN
            r.digits.[i] <- m
            let c = d
            mulP (i+1) n c p q r


    let mul p q =
        let rbound = p.used + q.used
        let r = createZero rbound
        let c = 0
        mulP 0 rbound c p q r
        normN r

    // --------------------------------------------------------

    [<EntryPoint>]
    let main argv = 
        let p = embed -12345
        let q = embed 67890
        let r = sub p q
        // let r = mul p q
        printfn "p = %A" (bshow p)
        printfn "q = %A" (bshow q)
        printfn "r = %A" (bshow r)
        0 // return an integer exit code

