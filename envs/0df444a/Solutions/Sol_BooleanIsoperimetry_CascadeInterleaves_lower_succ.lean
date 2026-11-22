-- Prove2me | solution 1 for BooleanIsoperimetry.CascadeInterleaves.lower_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:32.799281+00:00
-- url     : https://prove2.me/submissions/96ad7b00-b83d-46b6-86ad-1a2c470df62f

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
public import Theorems.Thm_BooleanIsoperimetry_splitPrefixMass_succ_of_cascadeSplits

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
namespace CascadeInterleaves
theorem _root_.solution
    {n a b p q p0 p1 q0 q1 a0 a1 b0 b1 : ℕ}
    (h_inter : CascadeInterleaves (n + 1) p q a b)
    (hp : CascadeSplit n p p0 p1) (hq : CascadeSplit n q q0 q1)
    (ha : CascadeSplit n a a0 a1) (hb : CascadeSplit n b b0 b1) :
    ∀ l, splitPrefixMass n a0 b0 (l + 1) + splitPrefixMass n a1 b1 l
        ≤ splitPrefixMass n p0 q0 (l + 1) + splitPrefixMass n p1 q1 l := by
  intro l
  have h_ineq := h_inter.2 (l + 1)
  rw [splitPrefixMass_succ_of_cascadeSplits ha hb] at h_ineq
  rw [splitPrefixMass_succ_of_cascadeSplits hp hq] at h_ineq
  exact h_ineq
end CascadeInterleaves
end BooleanIsoperimetry
