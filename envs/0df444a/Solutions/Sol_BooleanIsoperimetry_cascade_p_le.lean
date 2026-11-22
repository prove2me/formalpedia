-- Prove2me | solution 1 for BooleanIsoperimetry.cascade_p_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:08.132903+00:00
-- url     : https://prove2.me/submissions/1b7601b1-40cc-4c5d-a1c7-706893df7499

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Theorems.Thm_BooleanIsoperimetry_cascadeSlice0Value_le


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k p q : ℕ} (h : CascadeSplit n k p q) : p ≤ 2 ^ n := by
  obtain ⟨r, t, ht, h1, h2⟩ := h
  exact h1 ▸ cascadeSlice0Value_le ht
end BooleanIsoperimetry
