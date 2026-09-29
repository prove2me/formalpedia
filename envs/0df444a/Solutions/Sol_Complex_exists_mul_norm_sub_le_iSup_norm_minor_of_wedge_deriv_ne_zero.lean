-- Prove2me | solution 1 for Complex.exists_mul_norm_sub_le_iSup_norm_minor_of_wedge_deriv_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e448620d-9a19-56d9-b09a-b85aeb8a4f58

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_exists_mul_norm_sub_le_iSup_norm_minor_of_wedge_deriv_ne_zero

theorem solution {r : ℕ} {φ : ℂ → Fin r → ℂ} {c : ℂ}
    {R : ℝ} (hR : 0 < R) (hφ : ∀ i, DifferentiableOn ℂ (fun z ↦ φ z i) (Metric.ball c R))
    (hw : ∃ p : Fin r × Fin r,
      φ c p.1 * deriv (fun z ↦ φ z p.2) c - φ c p.2 * deriv (fun z ↦ φ z p.1) c ≠ 0) :
    ∃ ρ > 0, ∃ C > 0, ∀ z ∈ Metric.ball c ρ, ∀ w ∈ Metric.ball c ρ,
      C * ‖z - w‖ ≤ ⨆ p : Fin r × Fin r, ‖φ z p.1 * φ w p.2 - φ z p.2 * φ w p.1‖ := by
  obtain ⟨⟨i, j⟩, hW₀⟩ := hw
  simp only at hW₀

  set d : Fin r → ℂ → ℂ := fun k ξ ↦ deriv (fun z ↦ φ z k) ξ with hd
  set D : ℂ × ℂ → ℂ := fun q ↦ φ q.1 i * d j q.2 - φ q.1 j * d i q.2 with hD
  set W₀ : ℂ := D (c, c) with hW₀def
  have hW₀' : W₀ ≠ 0 := hW₀
  set η : ℝ := ‖W₀‖ / 8 with hη
  have hη0 : 0 < η := by positivity

  have hdiff : ∀ k, ∀ ξ ∈ Metric.ball c R, HasDerivAt (fun z ↦ φ z k) (d k ξ) ξ := fun k ξ hξ ↦
    ((hφ k).differentiableAt (Metric.isOpen_ball.mem_nhds hξ)).hasDerivAt
  have hdcont : ∀ k, ContinuousOn (d k) (Metric.ball c R) := fun k ↦
    ((hφ k).deriv Metric.isOpen_ball).continuousOn
  have hφcont : ∀ k, ContinuousOn (fun z ↦ φ z k) (Metric.ball c R) := fun k ↦ (hφ k).continuousOn
  have hcR : c ∈ Metric.ball c R := Metric.mem_ball_self hR

  have hDc : ContinuousAt D (c, c) := by
    have h1 : ∀ k, ContinuousAt (fun q : ℂ × ℂ ↦ φ q.1 k) (c, c) := fun k ↦
      ContinuousAt.comp' (f := Prod.fst) ((hφcont k).continuousAt (Metric.isOpen_ball.mem_nhds hcR)) continuousAt_fst
    have h2 : ∀ k, ContinuousAt (fun q : ℂ × ℂ ↦ d k q.2) (c, c) := fun k ↦
      ContinuousAt.comp' (f := Prod.snd) ((hdcont k).continuousAt (Metric.isOpen_ball.mem_nhds hcR)) continuousAt_snd
    exact ((h1 i).mul (h2 j)).sub ((h1 j).mul (h2 i))

  obtain ⟨ρ₁, hρ₁, hρ₁D⟩ := Metric.continuousAt_iff.mp hDc η hη0
  refine ⟨min ρ₁ R, lt_min hρ₁ hR, 5 * η, by positivity, fun z hz w hw ↦ ?_⟩
  have hzR : z ∈ Metric.ball c R := Metric.ball_subset_ball (min_le_right _ _) hz
  have hz₁ : dist z c < ρ₁ := lt_of_lt_of_le hz (min_le_left _ _)
  have hsub : Metric.ball c (min ρ₁ R) ⊆ Metric.ball c R := Metric.ball_subset_ball (min_le_right _ _)

  have hDη : ∀ ξ ∈ Metric.ball c (min ρ₁ R), dist (D (z, ξ)) W₀ < η := fun ξ hξ ↦ by
    apply hρ₁D
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨hz₁, lt_of_lt_of_le hξ (min_le_left _ _)⟩

  set f : ℂ → ℂ := fun ξ ↦ φ z i * φ ξ j - φ z j * φ ξ i - (ξ - z) * D (z, z) with hf
  have hfd : ∀ ξ ∈ Metric.ball c (min ρ₁ R),
      HasDerivWithinAt f (D (z, ξ) - D (z, z)) (Metric.ball c (min ρ₁ R)) ξ := by
    intro ξ hξ
    apply HasDerivAt.hasDerivWithinAt
    have e : D (z, ξ) - D (z, z) = φ z i * d j ξ - φ z j * d i ξ - 1 * D (z, z) := by
      simp only [hD]; ring
    rw [e]
    exact (((hdiff j ξ (hsub hξ)).const_mul (φ z i)).sub ((hdiff i ξ (hsub hξ)).const_mul (φ z j))).sub
      (((hasDerivAt_id ξ).sub_const z).mul_const (D (z, z)))
  have hbound : ∀ ξ ∈ Metric.ball c (min ρ₁ R), ‖D (z, ξ) - D (z, z)‖ ≤ 2 * η := by
    intro ξ hξ
    have h1 := hDη ξ hξ
    have h2 := hDη z hz
    rw [dist_eq_norm] at h1 h2
    calc ‖D (z, ξ) - D (z, z)‖ = ‖(D (z, ξ) - W₀) - (D (z, z) - W₀)‖ := by ring_nf
      _ ≤ ‖D (z, ξ) - W₀‖ + ‖D (z, z) - W₀‖ := norm_sub_le _ _
      _ ≤ 2 * η := by linarith
  have hmv := (convex_ball c (min ρ₁ R)).norm_image_sub_le_of_norm_hasDerivWithin_le hfd hbound hz hw
  have hfz : f z = 0 := by simp only [hf]; ring
  have hfw : f w = (φ z i * φ w j - φ z j * φ w i) - (w - z) * D (z, z) := rfl
  rw [hfz, sub_zero, hfw] at hmv

  have hWz : 7 * η ≤ ‖D (z, z)‖ := by
    have h2 := hDη z hz
    rw [dist_eq_norm] at h2
    have : ‖W₀‖ = 8 * η := by rw [hη]; ring
    have := norm_sub_norm_le W₀ (D (z, z))
    rw [norm_sub_rev] at h2
    linarith

  have hmain : 5 * η * ‖z - w‖ ≤ ‖φ z i * φ w j - φ z j * φ w i‖ := by
    have h1 : ‖(w - z) * D (z, z)‖ - ‖φ z i * φ w j - φ z j * φ w i‖ ≤ 2 * η * ‖w - z‖ := by
      calc ‖(w - z) * D (z, z)‖ - ‖φ z i * φ w j - φ z j * φ w i‖
          ≤ ‖φ z i * φ w j - φ z j * φ w i - (w - z) * D (z, z)‖ := by
            rw [← norm_neg (φ z i * φ w j - φ z j * φ w i - (w - z) * D (z, z)), neg_sub]
            exact norm_sub_norm_le _ _
        _ ≤ 2 * η * ‖w - z‖ := hmv
    rw [norm_mul] at h1
    have h3 : 7 * η * ‖w - z‖ ≤ ‖w - z‖ * ‖D (z, z)‖ := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left hWz (norm_nonneg _)
    rw [norm_sub_rev z w]
    linarith
  refine hmain.trans ?_
  exact le_ciSup (f := fun p : Fin r × Fin r ↦ ‖φ z p.1 * φ w p.2 - φ z p.2 * φ w p.1‖)
    (Set.finite_range _).bddAbove (i, j)

end S_Complex_exists_mul_norm_sub_le_iSup_norm_minor_of_wedge_deriv_ne_zero
end P2MW
export P2MW.S_Complex_exists_mul_norm_sub_le_iSup_norm_minor_of_wedge_deriv_ne_zero (solution)
