-- Prove2me | solution 1 for Egrs75.RepairDV.topBadIndex_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:39:10.342748+00:00
-- url     : https://prove2.me/submissions/a0ed6f59-24a6-49d3-af4a-ff4d00385bc5

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
theorem _root_.solution {q n : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n) :
    topBadIndex q n ∈ badIndexSet q n := by
  rw [topBadIndex, dif_pos (badIndexSet_nonempty hq hbad)]
  exact (badIndexSet q n).max'_mem _
end Egrs75.RepairDV
