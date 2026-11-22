-- Prove2me | solution 1 for BooleanIsoperimetry.cascade_upper_zero_eq_zero_or_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:26.715103+00:00
-- url     : https://prove2.me/submissions/c20fcf85-6901-47ff-b058-057919db69db

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
public import Theorems.Thm_BooleanIsoperimetry_cascade_upper_zero_eq_one

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n q q0 q1 : ℕ}
    (h : CascadeSplit n q q0 q1) (hq1_zero : q1 = 0) :
    q = 0 ∨ q = 1 := by
  by_cases hq_pos : 1 ≤ q
  · exact Or.inr (cascade_upper_zero_eq_one h hq_pos hq1_zero)
  · exact Or.inl (by omega)
end BooleanIsoperimetry
