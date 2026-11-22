-- Prove2me | solution 1 for BooleanIsoperimetry.HIncrement_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:20.733798+00:00
-- url     : https://prove2.me/submissions/9eac449c-812c-45e0-94d8-283c7c87c12a

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
public import Theorems.Thm_BooleanIsoperimetry_H_increment_lower_dim_sub
public import Theorems.Thm_BooleanIsoperimetry_H_mono


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n p : ℕ) (hp : p + 1 ≤ 2 ^ n) :
    n - p ≤ HIncrement n p := by
  unfold HIncrement
  have hmono : H n p ≤ H n (p + 1) := H_mono (by omega)
  have h := H_increment_lower_dim_sub n p hp
  omega
end BooleanIsoperimetry
