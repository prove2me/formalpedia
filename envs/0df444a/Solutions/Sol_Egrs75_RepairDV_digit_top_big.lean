-- Prove2me | solution 1 for Egrs75.RepairDV.digit_top_big
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:39:45.982175+00:00
-- url     : https://prove2.me/submissions/e3d51661-8299-4930-ac90-1a72e027c300

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Theorems.Thm_Egrs75_RepairDV_topBadIndex_mem

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RepairDV
open Nat
open Egrs75
open Egrs75.LeafInduction
namespace Egrs75.RepairDV
theorem _root_.solution {q n : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n) :
    (q - 1) / 2 < n / q ^ (topBadIndex q n) % q := by
  have hmem := topBadIndex_mem hq hbad
  simp only [badIndexSet, Finset.mem_filter, Finset.mem_range] at hmem
  obtain ⟨hlt, hbig⟩ := hmem
  rw [getD_digits n _ (by omega)] at hbig
  simpa only [bigQ, decide_eq_true_eq] using hbig
end Egrs75.RepairDV
