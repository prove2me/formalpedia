-- Prove2me | solution 1 for BooleanIsoperimetry.H_binomPrefix_partial_window_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:46.643232+00:00
-- url     : https://prove2.me/submissions/a2cc9fe1-768a-4619-8c85-ccac49f74c8d

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
public import Theorems.Thm_BooleanIsoperimetry_H_binomPrefix_window

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n r s t : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s)
    (ht : t ≤ (Finset.Ico (r + 1) (s + 1)).sum (fun i => Nat.choose n i)) :
    H n (binomPrefix n r) + t ≤ H n (binomPrefix n s) := by
  rw [← H_binomPrefix_window n r s hr hrs]
  omega
end BooleanIsoperimetry
