-- Prove2me | solution 1 for ContinualHardness.Linear.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T21:29:14.146661+00:00
-- url     : https://prove2.me/submissions/697b9c89-3256-4e15-aadd-6fa1288cbed8

import Mathlib

open MeasureTheory ProbabilityTheory

/-- §A.1, Eq. (6), p. 16 (Gaussian anti-concentration). For `g ∼ N(0, σ²)` with `σ > 0`, every
`t ∈ ℝ` and every `δ ≥ 0`: `Pr[g ∈ [t, t + δ]] ≤ δ/(σ√(2π))`. -/
theorem solution (σ t δ : ℝ) (hσ : 0 < σ) (hδ : 0 ≤ δ) :
    (gaussianReal 0 (σ ^ 2).toNNReal (Set.Icc t (t + δ))).toReal
      ≤ δ / (σ * Real.sqrt (2 * Real.pi)) := by
  have hv : (σ ^ 2).toNNReal ≠ 0 := by
    simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity
  have hvc : ((σ ^ 2).toNNReal : ℝ) = σ ^ 2 := Real.coe_toNNReal _ (by positivity)
  rw [gaussianReal_apply_eq_integral _ hv, ENNReal.toReal_ofReal]
  · have hC : ∀ x ∈ Set.Icc t (t + δ), ‖gaussianPDFReal 0 (σ ^ 2).toNNReal x‖
        ≤ (σ * Real.sqrt (2 * Real.pi))⁻¹ := by
      intro x _
      rw [Real.norm_of_nonneg (gaussianPDFReal_nonneg _ _ _), gaussianPDFReal_def]
      simp only [hvc]
      have h1 : Real.sqrt (2 * Real.pi * σ ^ 2) = σ * Real.sqrt (2 * Real.pi) := by
        rw [show 2 * Real.pi * σ ^ 2 = σ ^ 2 * (2 * Real.pi) by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq hσ.le]
      rw [h1]
      have : Real.exp (-(x - 0) ^ 2 / (2 * σ ^ 2)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ (x - 0) ^ 2 / (2 * σ ^ 2) := by positivity
        rw [neg_div]; linarith
      calc _ ≤ (σ * Real.sqrt (2 * Real.pi))⁻¹ * 1 := by gcongr
        _ = _ := mul_one _
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc t (t + δ))
      (by simp) hC
    have hvol : volume.real (Set.Icc t (t + δ)) = δ := by
      simp [Measure.real, hδ]
    rw [hvol] at this
    calc _ ≤ ‖∫ x in Set.Icc t (t + δ), gaussianPDFReal 0 (σ ^ 2).toNNReal x‖ := le_abs_self _
      _ ≤ _ := this
      _ = _ := by rw [div_eq_mul_inv]; ring
  · exact integral_nonneg (fun _ => gaussianPDFReal_nonneg _ _ _)
