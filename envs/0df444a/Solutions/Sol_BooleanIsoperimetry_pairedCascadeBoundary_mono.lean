-- Prove2me | solution 1 for BooleanIsoperimetry.pairedCascadeBoundary_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:57.85606+00:00
-- url     : https://prove2.me/submissions/b4c66692-e317-433f-8614-66cd0f0f983d

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
public import Theorems.Thm_BooleanIsoperimetry_cascadeBoundary_mono

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n x0 x1 y0 y1 z0 z1 w0 w1 : ℕ}
    (hx0 : x0 ≤ z0) (hx1 : x1 ≤ z1) (hy0 : y0 ≤ w0) (hy1 : y1 ≤ w1) :
    pairedCascadeBoundary n x0 x1 y0 y1 ≤ pairedCascadeBoundary n z0 z1 w0 w1 := by
  unfold pairedCascadeBoundary
  exact Nat.add_le_add (cascadeBoundary_mono hx0 hx1) (cascadeBoundary_mono hy0 hy1)
end BooleanIsoperimetry
