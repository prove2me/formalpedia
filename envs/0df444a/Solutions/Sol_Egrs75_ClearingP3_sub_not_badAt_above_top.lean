-- Prove2me | solution 1 for Egrs75.ClearingP3.sub_not_badAt_above_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:40:20.538797+00:00
-- url     : https://prove2.me/submissions/2da1514b-5055-4a72-b587-fc6978fe2ad8

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.Nat.Factorization.Defs
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
public import Theorems.Thm_Egrs75_ClearingP3_sub_high_digits_frozen
public import Theorems.Thm_Egrs75_RepairDV_digit_good_above_top


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
theorem _root_.solution {q : ℕ} (hq : q.Prime) {n S : ℕ}
    (hbad : 0 < badCountQ q n) (hS : S ≤ n % q ^ (topBadIndex q n)) {idx : ℕ}
    (hidx : topBadIndex q n < idx) :
    ¬ BadAt q idx (n - S) := by
  have hq1 : 1 < q := hq.one_lt
  unfold BadAt digitAt
  rw [sub_high_digits_frozen (by omega) hS (le_of_lt hidx)]
  have := digit_good_above_top hq1 hbad hidx
  omega
end Egrs75.ClearingP3
