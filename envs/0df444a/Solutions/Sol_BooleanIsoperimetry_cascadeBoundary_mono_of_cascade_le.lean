-- Prove2me | solution 1 for BooleanIsoperimetry.cascadeBoundary_mono_of_cascade_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:58.455721+00:00
-- url     : https://prove2.me/submissions/a04e9c47-6053-483c-aa4b-6941e6928544

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
public import Theorems.Thm_BooleanIsoperimetry_cascade_slice_mono
public import Theorems.Thm_BooleanIsoperimetry_cascadeBoundary_mono

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n x x0 x1 y y0 y1 : ℕ}
    (hx : CascadeSplit n x x0 x1) (hy : CascadeSplit n y y0 y1) (hxy : x ≤ y) :
    cascadeBoundary n x0 x1 ≤ cascadeBoundary n y0 y1 := by
  obtain ⟨h0, h1⟩ := cascade_slice_mono hx hy hxy
  exact cascadeBoundary_mono h0 h1
end BooleanIsoperimetry
