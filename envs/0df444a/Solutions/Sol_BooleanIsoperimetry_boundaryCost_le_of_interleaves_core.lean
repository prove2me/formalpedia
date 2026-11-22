-- Prove2me | solution 1 for BooleanIsoperimetry.boundaryCost_le_of_interleaves_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:52:46.660356+00:00
-- url     : https://prove2.me/submissions/ea60d8b9-7032-4563-b5cb-d380b071fdf2

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
public import Theorems.Thm_BooleanIsoperimetry_CascadeInterleaves_cascade
public import Theorems.Thm_BooleanIsoperimetry_boundaryCost_le_of_LE_GT_sums

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n p q a b : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (h_inter : CascadeInterleaves (n + 1) p q a b) :
    max (H (n + 1) p) q + max (H (n + 1) q) p ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by
  have hpq_casc : CascadeSplit (n + 1) (a + b) p q := h_inter.cascade
  rcases le_total b a with hba | hab
  · exact boundaryCost_le_of_LE_GT_sums n ih ha hb hpq_casc hba
  · have hpq_casc' : CascadeSplit (n + 1) (b + a) p q := by
      rwa [Nat.add_comm a b] at hpq_casc
    have h := boundaryCost_le_of_LE_GT_sums n ih hb ha hpq_casc' hab
    rw [Nat.add_comm (max (H (n + 1) a) b) (max (H (n + 1) b) a)]
    exact h
end BooleanIsoperimetry
