-- Prove2me | solution 1 for BooleanIsoperimetry.card_initSeg_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:40.803131+00:00
-- url     : https://prove2.me/submissions/15864e06-ef37-4a3e-b6a2-89a56e4d2ae5

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_card_simplicialInitSeg
public import Theorems.Thm_BooleanIsoperimetry_initSeg_nested
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n a b : ℕ} (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) :
    (simplicialInitSeg n a ∪ simplicialInitSeg n b).card = max a b := by
  cases le_total a b <;>
    simp_all +decide only [initSeg_nested, Finset.union_eq_right.mpr, sup_of_le_right,
      sup_of_le_left]
  · rw [card_simplicialInitSeg, min_eq_left hb]
  · rw [Finset.union_eq_left.mpr (initSeg_nested ‹_›), card_simplicialInitSeg]; aesop
end BooleanIsoperimetry
