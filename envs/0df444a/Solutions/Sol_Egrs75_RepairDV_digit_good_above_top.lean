-- Prove2me | solution 1 for Egrs75.RepairDV.digit_good_above_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:39:45.036309+00:00
-- url     : https://prove2.me/submissions/3c8b9b6c-74a6-43e3-bdba-20c225a737bc

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Theorems.Thm_Egrs75_RepairDV_le_topBadIndex

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RepairDV
open Nat
open Egrs75
open Egrs75.LeafInduction
namespace Egrs75.RepairDV
theorem _root_.solution {q n i : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n)
    (hi : topBadIndex q n < i) : n / q ^ i % q ≤ (q - 1) / 2 := by
  -- The digit at index `i` equals `(digits q n).getD i 0`.
  have hval : n / q ^ i % q = (Nat.digits q n).getD i 0 :=
    (getD_digits n i (by omega)).symm
  by_cases hlen : i < (Nat.digits q n).length
  · -- in range: if it were oversized, `i` would be a bad index `> topBadIndex`,
    -- contradicting maximality.
    by_contra hcon
    push Not at hcon
    have hibad : i ∈ badIndexSet q n := by
      simp only [badIndexSet, Finset.mem_filter, Finset.mem_range]
      simp_all
    have := le_topBadIndex hq hbad hibad
    omega
  · -- out of range: the digit reads as the default `0`.
    simp_all
end Egrs75.RepairDV
