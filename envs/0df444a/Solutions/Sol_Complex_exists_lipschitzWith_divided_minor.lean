-- Prove2me | solution 1 for Complex.exists_lipschitzWith_divided_minor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d086be8d-3dbf-59c5-ad84-78a6478d2f5c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_exists_lipschitzWith_divided_minor

open Metric

theorem solution {r : ℕ} {φ : ℂ → Fin r → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hφ : ∀ i, DifferentiableOn ℂ (fun z ↦ φ z i) (Metric.ball c R)) :
    ∃ ρ > 0, ∃ L ≥ 0, ∃ Ψ : ℂ → ℂ → (Fin r × Fin r → ℂ),
      (∀ w ∈ Metric.ball c ρ, ∀ z ∈ Metric.ball c ρ, ∀ p : Fin r × Fin r,
          φ w p.1 * φ z p.2 - φ w p.2 * φ z p.1 = (z - w) * Ψ w z p) ∧
      (∀ w ∈ Metric.ball c ρ, ∀ p : Fin r × Fin r,
          Ψ w w p = φ w p.1 * deriv (fun z ↦ φ z p.2) w - φ w p.2 * deriv (fun z ↦ φ z p.1) w) ∧
      (∀ w ∈ Metric.ball c ρ, ∀ z ∈ Metric.ball c ρ, ∀ z' ∈ Metric.ball c ρ,
          ‖Ψ w z - Ψ w z'‖ ≤ L * ‖z - z'‖) := by

  set f : Fin r → ℂ → ℂ := fun k z ↦ φ z k with hf
  set D : Fin r → ℂ → ℂ → ℂ := fun k w z ↦ dslope (f k) w z with hD
  have hfd : ∀ k, DifferentiableOn ℂ (f k) (ball c R) := hφ

  have hDdiff : ∀ k, ∀ w ∈ ball c R, DifferentiableOn ℂ (D k w) (ball c R) := by
    intro k w hw z hz
    by_cases hzw : z = w
    · have ha : AnalyticAt ℂ (f k) w := (hfd k).analyticAt (isOpen_ball.mem_nhds hw)
      obtain ⟨p, hp⟩ := ha
      rw [hzw]
      exact hp.has_fpower_series_dslope_fslope.analyticAt.differentiableAt.differentiableWithinAt
    · exact ((differentiableAt_dslope_of_ne hzw).2
        ((hfd k).differentiableAt (isOpen_ball.mem_nhds hz))).differentiableWithinAt

  set K : Set ℂ := closedBall c (R / 2) with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hKsub : K ⊆ ball c R := closedBall_subset_ball (by linarith)
  have hM₀ : ∀ k, ∃ C, ∀ z ∈ K, ‖f k z‖ ≤ C := fun k ↦
    hKc.exists_bound_of_continuousOn ((hfd k).continuousOn.mono hKsub)
  have hM₁ : ∀ k, ∃ C, ∀ z ∈ K, ‖deriv (f k) z‖ ≤ C := fun k ↦
    hKc.exists_bound_of_continuousOn (((hfd k).deriv isOpen_ball).continuousOn.mono hKsub)
  choose C₀ hC₀ using hM₀
  choose C₁ hC₁ using hM₁
  set M₀ : ℝ := ∑ k, |C₀ k| with hM₀def
  set M₁ : ℝ := ∑ k, |C₁ k| with hM₁def
  have hM₀nn : 0 ≤ M₀ := Finset.sum_nonneg fun k _ ↦ abs_nonneg _
  have hM₁nn : 0 ≤ M₁ := Finset.sum_nonneg fun k _ ↦ abs_nonneg _
  have hφM₀ : ∀ k, ∀ z ∈ K, ‖f k z‖ ≤ M₀ := fun k z hz ↦
    ((hC₀ k z hz).trans (le_abs_self _)).trans
      (Finset.single_le_sum (f := fun k ↦ |C₀ k|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ k))
  have hφM₁ : ∀ k, ∀ z ∈ K, ‖deriv (f k) z‖ ≤ M₁ := fun k z hz ↦
    ((hC₁ k z hz).trans (le_abs_self _)).trans
      (Finset.single_le_sum (f := fun k ↦ |C₁ k|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ k))

  have hDbound : ∀ k, ∀ w ∈ K, ∀ ζ ∈ K, ‖D k w ζ‖ ≤ M₁ := by
    intro k w hw ζ hζ
    by_cases hζw : ζ = w
    · rw [hζw]
      simp only [hD, dslope_same]
      exact hφM₁ k w hw
    · have hmv : ‖f k ζ - f k w‖ ≤ M₁ * ‖ζ - w‖ :=
        (convex_closedBall c (R / 2)).norm_image_sub_le_of_norm_deriv_le
          (fun x hx ↦ (hfd k).differentiableAt (isOpen_ball.mem_nhds (hKsub hx)))
          (hφM₁ k) hw hζ
      simp only [hD, dslope_of_ne _ hζw, slope_def_module]
      rw [norm_smul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.2 (sub_ne_zero.2 hζw)), mul_comm]
      exact hmv

  have hR4 : 0 < R / 4 := by positivity
  have hDderiv : ∀ k, ∀ w ∈ K, ∀ z ∈ ball c (R / 4), ‖deriv (D k w) z‖ ≤ M₁ / (R / 4) := by
    intro k w hw z hz
    have hsub : closedBall z (R / 4) ⊆ K := by
      intro ζ hζ
      simp only [hK, mem_closedBall] at hζ ⊢
      have := mem_ball.1 hz
      linarith [dist_triangle ζ z c]
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR4 ?_ ?_
    · apply DifferentiableOn.diffContOnCl
      rw [closure_ball z hR4.ne']
      exact (hDdiff k w (hKsub hw)).mono (hsub.trans hKsub)
    · intro ζ hζ
      exact hDbound k w hw ζ (hsub (sphere_subset_closedBall hζ))

  have hDlip : ∀ k, ∀ w ∈ K, ∀ z ∈ ball c (R / 4), ∀ z' ∈ ball c (R / 4),
      ‖D k w z - D k w z'‖ ≤ M₁ / (R / 4) * ‖z - z'‖ := by
    intro k w hw z hz z' hz'
    have hsub : ball c (R / 4) ⊆ ball c R := ball_subset_ball (by linarith)
    exact (convex_ball c (R / 4)).norm_image_sub_le_of_norm_deriv_le
      (fun x hx ↦ (hDdiff k w (hKsub hw)).differentiableAt (isOpen_ball.mem_nhds (hsub hx)))
      (hDderiv k w hw) hz' hz

  have hρK : ball c (R / 4) ⊆ K := fun z hz ↦ by
    simp only [hK, mem_closedBall]
    have := mem_ball.1 hz
    linarith
  have hLnn : 0 ≤ 2 * M₀ * (M₁ / (R / 4)) :=
    mul_nonneg (mul_nonneg two_pos.le hM₀nn) (div_nonneg hM₁nn hR4.le)
  refine ⟨R / 4, hR4, 2 * M₀ * (M₁ / (R / 4)), hLnn,
    fun w z p ↦ f p.1 w * D p.2 w z - f p.2 w * D p.1 w z, ?_, ?_, ?_⟩
  · intro w _ z _ p
    have h1 := sub_smul_dslope (f p.2) w z
    have h2 := sub_smul_dslope (f p.1) w z
    simp only [smul_eq_mul] at h1 h2
    simp only [hD, hf] at h1 h2 ⊢
    linear_combination -(φ w p.1) * h1 + φ w p.2 * h2
  · intro w _ p
    simp only [hD, hf, dslope_same]
  · intro w hw z hz z' hz'
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun p ↦ ?_
    change ‖(f p.1 w * D p.2 w z - f p.2 w * D p.1 w z) - (f p.1 w * D p.2 w z' - f p.2 w * D p.1 w z')‖ ≤ _
    have e : f p.1 w * D p.2 w z - f p.2 w * D p.1 w z - (f p.1 w * D p.2 w z' - f p.2 w * D p.1 w z')
        = f p.1 w * (D p.2 w z - D p.2 w z') - f p.2 w * (D p.1 w z - D p.1 w z') := by ring
    rw [e]
    have hwK := hρK hw
    calc ‖f p.1 w * (D p.2 w z - D p.2 w z') - f p.2 w * (D p.1 w z - D p.1 w z')‖
        ≤ ‖f p.1 w * (D p.2 w z - D p.2 w z')‖ + ‖f p.2 w * (D p.1 w z - D p.1 w z')‖ := norm_sub_le _ _
      _ = ‖f p.1 w‖ * ‖D p.2 w z - D p.2 w z'‖ + ‖f p.2 w‖ * ‖D p.1 w z - D p.1 w z'‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ M₀ * (M₁ / (R / 4) * ‖z - z'‖) + M₀ * (M₁ / (R / 4) * ‖z - z'‖) :=
          add_le_add (mul_le_mul (hφM₀ _ w hwK) (hDlip _ w hwK z hz z' hz') (norm_nonneg _) hM₀nn)
            (mul_le_mul (hφM₀ _ w hwK) (hDlip _ w hwK z hz z' hz') (norm_nonneg _) hM₀nn)
      _ = 2 * M₀ * (M₁ / (R / 4)) * ‖z - z'‖ := by ring

end S_Complex_exists_lipschitzWith_divided_minor
end P2MW
export P2MW.S_Complex_exists_lipschitzWith_divided_minor (solution)
