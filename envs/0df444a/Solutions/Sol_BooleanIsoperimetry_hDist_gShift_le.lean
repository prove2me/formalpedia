-- Prove2me | solution 1 for BooleanIsoperimetry.hDist_gShift_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:33.278018+00:00
-- url     : https://prove2.me/submissions/18a45007-07c6-4394-b221-88466cfb08e2

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (v : Cube n) : hDist (gShift v) v ≤ 1 := by
  unfold hDist gShift
  split_ifs
  · simp_all +decide only [symmDiff, Finset.sup_eq_union']
    simp +decide only [Finset.min'_mem, Finset.sdiff_erase, sdiff_self,
      Finset.bot_eq_empty, insert_empty_eq, Finset.union_singleton, Finset.mem_sdiff,
      Finset.mem_erase, ne_eq, not_true_eq_false, and_true, and_self,
      not_false_eq_true, Finset.card_insert_of_notMem, add_le_iff_nonpos_left, nonpos_iff_eq_zero,
      Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]
    exact Finset.erase_subset _ _
  · simp_all +decide only [Finset.not_nonempty_iff_eq_empty, symmDiff, sdiff_self,
      Finset.bot_eq_empty,
      le_refl, sup_of_le_left, Finset.card_empty, zero_le]
end BooleanIsoperimetry
