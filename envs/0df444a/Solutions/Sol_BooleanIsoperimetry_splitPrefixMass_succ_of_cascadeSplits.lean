-- Prove2me | solution 1 for BooleanIsoperimetry.splitPrefixMass_succ_of_cascadeSplits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:42.347583+00:00
-- url     : https://prove2.me/submissions/7164ce7b-c31a-4ae4-89a6-bd2085e80755

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
public import Theorems.Thm_BooleanIsoperimetry_cappedPrefixMass_succ_of_cascadeSplit

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution
    (ha : CascadeSplit n a a0 a1) (hb : CascadeSplit n b b0 b1) (l : ℕ) :
    splitPrefixMass (n + 1) a b (l + 1)
      = splitPrefixMass n a0 b0 (l + 1) + splitPrefixMass n a1 b1 l := by
  unfold splitPrefixMass
  rw [cappedPrefixMass_succ_of_cascadeSplit ha, cappedPrefixMass_succ_of_cascadeSplit hb]
  omega
end BooleanIsoperimetry
