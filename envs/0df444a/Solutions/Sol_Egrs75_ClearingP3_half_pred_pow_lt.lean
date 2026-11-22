-- Prove2me | solution 1 for Egrs75.ClearingP3.half_pred_pow_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:02.603634+00:00
-- url     : https://prove2.me/submissions/a717d6d6-d235-49c7-a253-b37cca91aa41

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.Nat.Factorization.Defs
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch

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
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (m : ℕ) : (p ^ m - 1) / 2 < p ^ m := by
  have h1 : 1 ≤ p ^ m := Nat.one_le_pow _ _ (by omega)
  have : (p ^ m - 1) / 2 ≤ p ^ m - 1 := Nat.div_le_self _ _
  omega
end Egrs75.ClearingP3
