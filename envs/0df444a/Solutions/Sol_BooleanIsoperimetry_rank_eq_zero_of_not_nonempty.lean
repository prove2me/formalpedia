-- Prove2me | solution 1 for BooleanIsoperimetry.rank_eq_zero_of_not_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:02.166554+00:00
-- url     : https://prove2.me/submissions/1d61b2de-11b5-41d0-9aae-ab0add94104f

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
theorem _root_.solution {n p : ℕ} (w : Cube n) (hw : rank w = p)
    (hempty : ¬ w.Nonempty) : p = 0 := by
  have hwempty : w = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  rw [← hw]
  rw [hwempty]
  simp [rank, simplicialLt, simplicialLe]
end BooleanIsoperimetry
