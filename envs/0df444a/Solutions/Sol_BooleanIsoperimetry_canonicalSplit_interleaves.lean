-- Prove2me | solution 1 for BooleanIsoperimetry.canonicalSplit_interleaves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:31.099514+00:00
-- url     : https://prove2.me/submissions/5974185e-add9-4d7a-98e7-0410efb35acf

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
public import Theorems.Thm_BooleanIsoperimetry_splitPrefixMass_le_min
public import Theorems.Thm_BooleanIsoperimetry_cascade_splitPrefixMass_eq

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution
    {n a b p q : ℕ} (_ha : a ≤ 2 ^ n) (_hb : b ≤ 2 ^ n)
    (h_casc : CascadeSplit n (a + b) p q) :
    CascadeInterleaves n p q a b := by
  refine ⟨h_casc, fun l => ?_⟩
  have hub := splitPrefixMass_le_min n a b l
  have heq := cascade_splitPrefixMass_eq h_casc l
  rw [heq]
  exact hub
end BooleanIsoperimetry
