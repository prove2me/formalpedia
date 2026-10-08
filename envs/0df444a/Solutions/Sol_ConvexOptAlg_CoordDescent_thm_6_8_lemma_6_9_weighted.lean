-- Prove2me | solution 1 for ConvexOptAlg.CoordDescent.thm_6_8_lemma_6_9_weighted
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:53:21.150638+00:00
-- url     : https://prove2.me/submissions/be126487-cdf1-4733-8bd2-fe31d4dfc811

import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs

set_option autoImplicit false

open ConvexOptAlg.CoordDescent in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : Fin n → ℝ) (γ α : ℝ)
    (hβ : ∀ i, 0 < β i) (hα : 0 < α) (hsc : IsStronglyConvexWNorm f g β (1 - γ) α)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y) (x : EuclideanSpace ℝ (Fin n)) :
    2 * α * (f x - f xstar) ≤ wnormDual β (1 - γ) (g x) ^ 2 := by
  have hw : ∀ i, 0 < β i ^ (1 - γ) := fun i => Real.rpow_pos_of_pos (hβ i) _
  have h1 := hsc.2 x xstar
  unfold wnorm at h1
  unfold wnormDual
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_nonneg (hw i).le (sq_nonneg _))] at h1
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hw i).le)]
  have term : ∀ i, 2 * α * (g x i * (x i - xstar i)) - α ^ 2 * (β i ^ (1 - γ) * (x - xstar) i ^ 2)
      ≤ g x i ^ 2 / β i ^ (1 - γ) := by
    intro i
    have hwi := hw i
    have hd : (x - xstar) i = x i - xstar i := by simp
    rw [hd, le_div_iff₀ hwi]
    nlinarith [sq_nonneg (α * β i ^ (1 - γ) * (x i - xstar i) - g x i)]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => term i
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hα2 : 2 * α * (f x - f xstar) ≤
      2 * α * ((∑ i, g x i * (x i - xstar i)) -
        α / 2 * ∑ i, β i ^ (1 - γ) * (x - xstar) i ^ 2) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have e : 2 * α * ((∑ i, g x i * (x i - xstar i)) -
        α / 2 * ∑ i, β i ^ (1 - γ) * (x - xstar) i ^ 2) =
      2 * α * (∑ i, g x i * (x i - xstar i)) -
        α ^ 2 * ∑ i, β i ^ (1 - γ) * (x - xstar) i ^ 2 := by ring
  rw [e] at hα2
  exact le_trans hα2 hsum
