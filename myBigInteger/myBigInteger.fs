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
type BigNat =
    {mutable bound : int;
    digits : ints;
    }

module MyFirstBigInt =
    let maxInt a b = if a < b then b else (a:int)
    let minInt a b = if a < b then a else (b:int)
    let baseN = 10

    let rec pow32 x n =
        if n = 0 then 1
        elif n % 2 = 0 then pow32 (x * x) (n / 2)
        else                x * pow32 (x * x) (n / 2)

    let boundInt =
        let rec iter n i =
            if n > 1 then iter (n / baseN) (i+1) else i
        iter Int32.MaxValue 0

    let normN n =
        let rec findLeastIndex (d:ints) i =
            if i = -1 || d.[i] <> 0 then
                i + 1
            else
                findLeastIndex d (i - 1)
        let li = findLeastIndex n.digits (n.bound - 1)
        n.bound <- li
        n

    let createN n =
        {bound = n; digits = Array.zeroCreate n}
    
    let embed x =
        let x = if x < 0 then 0 else x
        if x < baseN then
            let r = createN 1
            r.digits.[0] <- x;
            normN r
        else
            let r = createN boundInt
            for i = 0 to boundInt - 1 do
                r.digits.[i] <- (x / pow32 baseN i) % baseN
            done
            normN r

    let index x i = if i < x.bound then x.digits.[i] else 0

    let zero = embed 0
    let one  = embed 1

    // --------------------------------------------------------

    let rec addP i n c p q r = // (p + q) + c
        if i < n then
            let x = index p i + index q i + c
            let d,m = x / baseN, x % baseN
            r.digits.[i] <- m
            let c = d
            addP (i+1) n c p q r

    let add p q = 
        let rbound = 1 + maxInt p.bound q.bound
        let r = createN rbound
        let carry = 0
        addP 0 rbound carry p q r;
        normN r
    
    let rec subP i n c p q r = // (p - q) + c
        if i < n then
            let x = index p i - index q i + c
            if x > 0 then
                let d, m = x / baseN, x % baseN
                r.digits.[i] <- m
                let c = d
                subP (i+1) n c p q r
            else
                let x = x + baseN
                let d, m = x / baseN, x % baseN
                r.digits.[i] <- m
                let c = d - 1
                subP (i+1) n c p q r
        else
            let underflow = c <> 0
            underflow

    let sub p q =
        let rbound = maxInt p.bound q.bound
        let r = createN rbound
        let c = 0
        let underflow = subP 0 rbound c p q r
        if underflow then  // p - q < 0
            embed 0
        else 
            normN r
    
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
        let rbound = p.bound + q.bound
        let r = createN rbound
        let c = 0
        mulP 0 rbound c p q r
        normN r

    // --------------------------------------------------------

    [<EntryPoint>]
    let main argv = 
        let p = embed 12345
        let q = embed 67890
        let r = mul p q
        printfn "p = %A" p
        printfn "q = %A" q
        printfn "r = %A" r
        0 // return an integer exit code

