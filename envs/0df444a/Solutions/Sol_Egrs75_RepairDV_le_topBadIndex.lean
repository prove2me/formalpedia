-- Prove2me | solution 1 for Egrs75.RepairDV.le_topBadIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:39:10.837919+00:00
-- url     : https://prove2.me/submissions/4eb070e6-e161-42bc-8f64-7c74d120c531

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Theorems.Thm_Egrs75_RepairDV_badIndexSet_nonempty

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RepairDV
open Nat
open Egrs75
open Egrs75.LeafInduction
namespace Egrs75.RepairDV
theorem _root_.solution {q n i : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n)
    (hi : i ∈ badIndexSet q n) : i ≤ topBadIndex q n := by
  rw [topBadIndex, dif_pos (badIndexSet_nonempty hq hbad)]
  exact (badIndexSet q n).le_max' i hi
end Egrs75.RepairDV
