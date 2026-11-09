-- Prove2me | solution 1 for AvramDividend.Classical.avram_b0dd16_finite_activity_masked_generator_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T17:11:15.652374+00:00
-- url     : https://prove2.me/submissions/1f0d0e7e-b04e-4d50-b708-edd39f094cf0

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b0dd16_finite_activity_generator_residual_lower

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite jump activity transfers integrability of sampled value to
    the masked signed generator residual without requiring a uniform
    positive-distance cutoff from zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (hMass : X.ν (Iio (0 : ℝ)) < ⊤)
    (hW : ∀ z : ℝ, 0 ≤ w z)
    (hDrift : 0 ≤ X.drift)
    (Y : Ω → ℝ) (mask : Ω → Prop)
    (hYI : Integrable (fun ω => w (Y ω)) P)
    (hInside : ∀ ω, mask ω →
      X.GeneratorIntegrable w (Y ω) ∧
        X.generator w (Y ω) - q * w (Y ω) ≤ 0 ∧
        0 ≤ deriv w (Y ω))
    (hMeas : AEStronglyMeasurable (fun ω =>
      if mask ω then X.generator w (Y ω) - q * w (Y ω) else 0) P) :
    Integrable (fun ω =>
      if mask ω then X.generator w (Y ω) - q * w (Y ω) else 0) P := by
  classical
  have hCoeff : 0 ≤ (X.ν (Iio (0 : ℝ))).toReal + q :=
    add_nonneg ENNReal.toReal_nonneg hq.le
  have hMajor : Integrable (fun ω =>
      ((X.ν (Iio (0 : ℝ))).toReal + q) * w (Y ω)) P := by
    simpa only [smul_eq_mul] using hYI.const_mul
      ((X.ν (Iio (0 : ℝ))).toReal + q)
  apply hMajor.mono' hMeas
  filter_upwards [] with ω
  have hMajNonneg :
      0 ≤ ((X.ν (Iio (0 : ℝ))).toReal + q) * w (Y ω) :=
    mul_nonneg hCoeff (hW (Y ω))
  by_cases hm : mask ω
  · have h := hInside ω hm
    have hLower := avram_b0dd16_finite_activity_generator_residual_lower
      X hBV q w (Y ω) h.1 hMass hW hDrift h.2.2
    have hUpper := h.2.1
    simp only [if_pos hm, Real.norm_eq_abs]
    rw [abs_of_nonpos hUpper]
    linarith
  · simp only [if_neg hm, Real.norm_eq_abs, abs_zero]
    simpa only [abs_of_nonneg hMajNonneg] using hMajNonneg
