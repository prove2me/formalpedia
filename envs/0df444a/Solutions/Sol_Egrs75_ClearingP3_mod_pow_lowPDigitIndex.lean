-- Prove2me | solution 1 for Egrs75.ClearingP3.mod_pow_lowPDigitIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:45.921296+00:00
-- url     : https://prove2.me/submissions/8cd25cdf-7c93-45ed-8799-3c1aeb03d146

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.Nat.Factorization.Defs
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
public import Theorems.Thm_Egrs75_ClearingP3_pow_lowPDigitIndex_dvd

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.ClearingP3
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
namespace Egrs75.ClearingP3
theorem _root_.solution {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) :
    n % p ^ (lowPDigitIndex p n) = 0 :=
  Nat.mod_eq_zero_of_dvd (pow_lowPDigitIndex_dvd hp hn)
end Egrs75.ClearingP3
