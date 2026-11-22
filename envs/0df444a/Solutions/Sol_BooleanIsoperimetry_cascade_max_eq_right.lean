-- Prove2me | solution 1 for BooleanIsoperimetry.cascade_max_eq_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:41.335326+00:00
-- url     : https://prove2.me/submissions/91ac5eb4-6199-43d8-b0c0-ced0e7662445

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
public import Theorems.Thm_BooleanIsoperimetry_H_zero
public import Theorems.Thm_BooleanIsoperimetry_cascade_p_le_H_q


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n x x0 x1 : ℕ} (hx : CascadeSplit n x x0 x1) :
    max (H n x1) x0 = if 1 ≤ x1 then H n x1 else x0 := by
  split_ifs with h
  · apply max_eq_left
    exact cascade_p_le_H_q hx h
  · have h0 : x1 = 0 := by omega
    subst h0
    rw [H_zero]
    exact max_eq_right (Nat.zero_le _)
end BooleanIsoperimetry
