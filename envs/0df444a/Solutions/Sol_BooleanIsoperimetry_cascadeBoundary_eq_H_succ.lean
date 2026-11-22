-- Prove2me | solution 1 for BooleanIsoperimetry.cascadeBoundary_eq_H_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:49.630589+00:00
-- url     : https://prove2.me/submissions/f199111f-017d-43c7-a14a-d487221a47d8

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
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n x x0 x1 : ℕ} (hx : CascadeSplit n x x0 x1) :
    cascadeBoundary n x0 x1 = H (n + 1) x := by
  unfold cascadeBoundary
  rw [H_succ_cascade hx]
end BooleanIsoperimetry
