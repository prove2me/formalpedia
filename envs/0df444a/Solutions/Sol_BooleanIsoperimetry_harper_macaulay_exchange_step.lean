-- Prove2me | solution 1 for BooleanIsoperimetry.harper_macaulay_exchange_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:50:49.834774+00:00
-- url     : https://prove2.me/submissions/92d8b7b8-e8eb-43e8-b2e0-42394d688e1e

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
public import Theorems.Thm_BooleanIsoperimetry_boundaryCost_le_of_lower_interleaves_step_live
public import Theorems.Thm_BooleanIsoperimetry_CascadeInterleaves_lower_succ
public import Theorems.Thm_BooleanIsoperimetry_canonicalSplit_interleaves
public import Theorems.Thm_BooleanIsoperimetry_cascade_p_le
public import Theorems.Thm_BooleanIsoperimetry_cascade_q_le
public import Theorems.Thm_BooleanIsoperimetry_exists_cascade_split


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ} (ha_cap : a ≤ 2 ^ (n + 1)) (hb_cap : b ≤ 2 ^ (n + 1))
    (hpq_casc : CascadeSplit (n + 1) (a + b) p q) :
    max (H (n + 1) p) q + max (H (n + 1) q) p ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by
  have hp_cap : p ≤ 2 ^ (n + 1) := cascade_p_le hpq_casc
  have hq_cap : q ≤ 2 ^ (n + 1) := cascade_q_le hpq_casc
  obtain ⟨p0, p1, _, _, _, hp⟩ := exists_cascade_split n p hp_cap
  obtain ⟨q0, q1, _, _, _, hq⟩ := exists_cascade_split n q hq_cap
  obtain ⟨a0, a1, _, _, _, ha⟩ := exists_cascade_split n a ha_cap
  obtain ⟨b0, b1, _, _, _, hb⟩ := exists_cascade_split n b hb_cap
  rcases le_total b a with hba | hab
  · have h_inter := canonicalSplit_interleaves ha_cap hb_cap hpq_casc
    have h_lower := CascadeInterleaves.lower_succ h_inter hp hq ha hb
    exact boundaryCost_le_of_lower_interleaves_step_live n p q a b
      p0 p1 q0 q1 a0 a1 b0 b1 ih ha_cap hb_cap hba hpq_casc hp hq ha hb h_lower
  · have hpq_casc' : CascadeSplit (n + 1) (b + a) p q := by
      rwa [Nat.add_comm a b] at hpq_casc
    have h_inter := canonicalSplit_interleaves hb_cap ha_cap hpq_casc'
    have h_lower := CascadeInterleaves.lower_succ h_inter hp hq hb ha
    have h := boundaryCost_le_of_lower_interleaves_step_live n p q b a
      p0 p1 q0 q1 b0 b1 a0 a1 ih hb_cap ha_cap hab hpq_casc' hp hq hb ha h_lower
    rw [Nat.add_comm (max (H (n + 1) a) b) (max (H (n + 1) b) a)]
    exact h
end BooleanIsoperimetry
