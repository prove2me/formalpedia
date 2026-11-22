-- Prove2me | solution 1 for BooleanIsoperimetry.cappedPrefixMass_succ_of_cascadeSplit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:03.270194+00:00
-- url     : https://prove2.me/submissions/9b2f7433-788b-428b-bf49-5138d5c481aa

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
public import Theorems.Thm_BooleanIsoperimetry_cascade_splitPrefixMass_eq
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_pascal


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution
    {n k k0 k1 : ℕ} (hk : CascadeSplit n k k0 k1) (l : ℕ) :
    cappedPrefixMass (n + 1) k (l + 1)
      = cappedPrefixMass n k0 (l + 1) + cappedPrefixMass n k1 l := by
  unfold cappedPrefixMass
  have h_pascal : binomPrefix (n + 1) (l + 1) = binomPrefix n (l + 1) + binomPrefix n l := by
    have h := binomPrefix_pascal n (l + 1)
    rw [Nat.add_sub_cancel] at h
    exact h
  rw [h_pascal]
  have h_eq := cascade_splitPrefixMass_eq hk l
  unfold splitPrefixMass at h_eq
  exact h_eq.symm
end BooleanIsoperimetry
