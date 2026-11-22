-- Prove2me | solution 1 for BooleanIsoperimetry.harper_macaulay_joint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:53:20.961722+00:00
-- url     : https://prove2.me/submissions/e99f8612-491f-4947-8126-2fad7ea7cb45

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
public import Theorems.Thm_BooleanIsoperimetry_boundaryCost_le_of_interleaves_core
public import Theorems.Thm_BooleanIsoperimetry_H_ge_self
public import Theorems.Thm_BooleanIsoperimetry_canonicalSplit_interleaves
public import Theorems.Thm_BooleanIsoperimetry_cascade_p_le
public import Theorems.Thm_BooleanIsoperimetry_cascade_p_le_H_q
public import Theorems.Thm_BooleanIsoperimetry_cascade_q_le_p


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ) {a b p q : ℕ}
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + max (H (n + 1) b) a := by
  have h_inter := canonicalSplit_interleaves ha hb hcasc
  have h_mono := boundaryCost_le_of_interleaves_core n p q a b ih ha hb h_inter
  have h_b_le_H_a : b ≤ H (n + 1) a := le_trans hba (H_ge_self (n + 1) a ha)
  have max1 : max (H (n + 1) a) b = H (n + 1) a := max_eq_left h_b_le_H_a
  have h_p_ge_q : q ≤ p := cascade_q_le_p hcasc
  have h_p_le : p ≤ 2 ^ (n + 1) := cascade_p_le hcasc
  have h_q_le_H_p : q ≤ H (n + 1) p := le_trans h_p_ge_q (H_ge_self (n + 1) p h_p_le)
  have max2 : max (H (n + 1) p) q = H (n + 1) p := max_eq_left h_q_le_H_p
  have h_p_le_H_q : p ≤ H (n + 1) q := cascade_p_le_H_q hcasc hq_pos
  have max3 : max (H (n + 1) q) p = H (n + 1) q := max_eq_left h_p_le_H_q
  rw [max1, max2, max3] at h_mono
  exact h_mono
end BooleanIsoperimetry
