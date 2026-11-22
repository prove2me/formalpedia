-- Prove2me | solution 1 for BooleanIsoperimetry.H_eq_sum_HIncrement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:55.767831+00:00
-- url     : https://prove2.me/submissions/1f6c94e6-a6db-4c98-86e6-62425e0d7ccd

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
public import Theorems.Thm_BooleanIsoperimetry_H_zero
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n k : ℕ) :
    H n k = ∑ p ∈ Finset.range k, HIncrement n p := by
  induction k with
  | zero => simp [H_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold HIncrement
    have hmono : H n k ≤ H n (k + 1) := H_mono (by omega)
    omega
end BooleanIsoperimetry
