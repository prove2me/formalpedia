-- Prove2me | solution 1 for BooleanIsoperimetry.cascade_split_binomPrefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:34.253284+00:00
-- url     : https://prove2.me/submissions/55fb7148-5104-47a2-a430-13b4e973da38

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
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n + 1) :
    CascadeSplit n (binomPrefix (n + 1) r) (binomPrefix n r) (binomPrefix n (r - 1)) := by
  have _hr_used : 1 ≤ r := hr
  refine ⟨r, 0, ?_, ?_, ?_⟩
  · refine ⟨by omega, by simp, by simp, ?_⟩
    left
    exact Nat.choose_pos hrn
  · unfold cascadeSlice0Value
    simp
  · unfold cascadeSlice1Value
    simp
end BooleanIsoperimetry
