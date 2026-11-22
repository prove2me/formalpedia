-- Prove2me | solution 1 for BooleanIsoperimetry.cascadeBoundary_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:10.04149+00:00
-- url     : https://prove2.me/submissions/4d13b2d2-11d5-4380-bcdd-f06c734f028a

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
public import Theorems.Thm_BooleanIsoperimetry_H_mono


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n x0 x1 y0 y1 : ℕ} (h0 : x0 ≤ y0) (h1 : x1 ≤ y1) :
    cascadeBoundary n x0 x1 ≤ cascadeBoundary n y0 y1 := by
  unfold cascadeBoundary
  exact Nat.add_le_add (max_le_max (H_mono h0) h1) (max_le_max (H_mono h1) h0)
end BooleanIsoperimetry
