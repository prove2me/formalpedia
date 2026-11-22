-- Prove2me | solution 1 for BooleanIsoperimetry.H_binomPrefix_succ_diff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:45.743074+00:00
-- url     : https://prove2.me/submissions/84157e0d-d777-4e83-8315-afde5eb431b8

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
public import Theorems.Thm_BooleanIsoperimetry_H_binomPrefix_diff
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n r : ℕ) (hr : 1 ≤ r) :
    H n (binomPrefix n (r + 1)) - H n (binomPrefix n r) =
      Nat.choose n (r + 1) := by
  simpa [Nat.succ_eq_add_one] using H_binomPrefix_diff n (r + 1) (by omega)
end BooleanIsoperimetry
