-- Prove2me | solution 1 for BooleanIsoperimetry.pairedCascadeBoundary_eq_H_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:57.244127+00:00
-- url     : https://prove2.me/submissions/a5cce170-4ca8-411f-ad06-61f9cdf2179f

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
public import Theorems.Thm_BooleanIsoperimetry_cascadeBoundary_eq_H_succ

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n x y x0 x1 y0 y1 : ℕ}
    (hx : CascadeSplit n x x0 x1) (hy : CascadeSplit n y y0 y1) :
    pairedCascadeBoundary n x0 x1 y0 y1 = H (n + 1) x + H (n + 1) y := by
  unfold pairedCascadeBoundary
  rw [cascadeBoundary_eq_H_succ hx, cascadeBoundary_eq_H_succ hy]
end BooleanIsoperimetry
