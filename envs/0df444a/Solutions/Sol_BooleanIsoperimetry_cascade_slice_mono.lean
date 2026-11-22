-- Prove2me | solution 1 for BooleanIsoperimetry.cascade_slice_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:02.896394+00:00
-- url     : https://prove2.me/submissions/8b4e16cf-3f28-43c1-85a9-229c5f52eec3

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
public import Theorems.Thm_BooleanIsoperimetry_initSeg_nested
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_slice_card_eq_cascade
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n x x0 x1 y y0 y1 : ℕ}
    (hx : CascadeSplit n x x0 x1) (hy : CascadeSplit n y y0 y1) (hxy : x ≤ y) :
    x0 ≤ y0 ∧ x1 ≤ y1 := by
  obtain ⟨hx0, hx1⟩ := slice_card_eq_cascade hx
  obtain ⟨hy0, hy1⟩ := slice_card_eq_cascade hy
  have hsub : simplicialInitSeg (n + 1) x ⊆ simplicialInitSeg (n + 1) y :=
    initSeg_nested hxy
  constructor
  · rw [← hx0, ← hy0]
    apply Finset.card_le_card
    intro v hv
    simp only [slice0, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hsub hv
  · rw [← hx1, ← hy1]
    apply Finset.card_le_card
    intro v hv
    simp only [slice1, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hsub hv
end BooleanIsoperimetry
