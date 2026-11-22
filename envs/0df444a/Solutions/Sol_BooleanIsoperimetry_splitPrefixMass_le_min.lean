-- Prove2me | solution 1 for BooleanIsoperimetry.splitPrefixMass_le_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:53.144748+00:00
-- url     : https://prove2.me/submissions/4da1582f-3c98-4d7b-b6db-b45bade9c6dd

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

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n a b l : ℕ) :
    splitPrefixMass n a b l ≤
      min (a + b) (binomPrefix n (l + 1) + binomPrefix n l) := by
  unfold splitPrefixMass cappedPrefixMass
  omega
end BooleanIsoperimetry
