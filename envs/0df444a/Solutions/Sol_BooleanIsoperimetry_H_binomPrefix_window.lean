-- Prove2me | solution 1 for BooleanIsoperimetry.H_binomPrefix_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:38:40.062738+00:00
-- url     : https://prove2.me/submissions/9af7f73f-2db3-46b5-adb7-54b0247cfaab

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
public import Theorems.Thm_BooleanIsoperimetry_H_binomPrefix

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n r s : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) :
    H n (binomPrefix n r) +
        (Finset.Ico (r + 1) (s + 1)).sum (fun i => Nat.choose n i) =
      H n (binomPrefix n s) := by
  rw [H_binomPrefix n r hr, H_binomPrefix n s (by omega)]
  exact Finset.sum_range_add_sum_Ico (fun i => Nat.choose n i) (by omega : r + 1 ≤ s + 1)
end BooleanIsoperimetry
