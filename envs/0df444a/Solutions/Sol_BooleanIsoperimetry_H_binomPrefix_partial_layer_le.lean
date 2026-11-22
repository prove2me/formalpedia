-- Prove2me | solution 1 for BooleanIsoperimetry.H_binomPrefix_partial_layer_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:46.149798+00:00
-- url     : https://prove2.me/submissions/bac42f03-f213-4bd7-ab18-810ccadc7faa

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
public import Theorems.Thm_BooleanIsoperimetry_H_binomPrefix_add_layer

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n r t : ℕ) (hr : 1 ≤ r)
    (ht : t ≤ Nat.choose n (r + 1)) :
    H n (binomPrefix n r) + t ≤ H n (binomPrefix n (r + 1)) := by
  rw [← H_binomPrefix_add_layer n r hr]
  omega
end BooleanIsoperimetry
