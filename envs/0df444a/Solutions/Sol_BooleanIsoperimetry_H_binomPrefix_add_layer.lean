-- Prove2me | solution 1 for BooleanIsoperimetry.H_binomPrefix_add_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:38:43.210868+00:00
-- url     : https://prove2.me/submissions/50f062f6-3dd8-4225-b0b1-61a09d2a76e1

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
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_succ


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n r : ℕ) (hr : 1 ≤ r) :
    H n (binomPrefix n r) + Nat.choose n (r + 1) =
      H n (binomPrefix n (r + 1)) := by
  rw [H_binomPrefix n r hr, H_binomPrefix n (r + 1) (by omega)]
  rw [binomPrefix_succ n (r + 1)]
end BooleanIsoperimetry
