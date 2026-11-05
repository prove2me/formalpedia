-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_BV_compact_HJB_drift_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:00:58.094275+00:00
-- url     : https://prove2.me/submissions/0f47e565-2f4a-4f95-8da6-d0f3e08d0259

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_uniform_physical_negative_levy_integral_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_negative_levy_tail_finite_at_BV_C1_threshold
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Uniform bound on the true source HJB drift, with BV Lévy tail discharged. -/
theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
(w : ℝ → ℝ) (hwMeas : Measurable w)
(q : ℝ) (a b L R A : ℝ)
(ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
(hL : 0 ≤ L) (hR : 0 ≤ R) (hA : 0 ≤ A)
(hLip : ∀ u ∈ Set.Icc (a / 2) b, ∀ v ∈ Set.Icc (a / 2) b,
  |w u - w v| ≤ L * |u - v|)
(hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
(hDeriv : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ A) :
∃ K : ℝ, 0 ≤ K ∧ ∀ y ∈ Set.Icc a b,
  |X.drift * deriv w y +
    (∫ z in Set.Iio (0 : ℝ), w (y + z) - w y ∂X.ν) - q * w y| ≤ K := by
  have hMass : X.ν (Iic (-a / 2)) < ⊤ :=
    avram_wave8_22_original_negative_levy_tail_finite_at_BV_C1_threshold
      X a ha ha2
  obtain ⟨M, hM, hJ⟩ :=
    avram_wave8_22_original_BV_uniform_physical_negative_levy_integral_bound
      X hBV w hwMeas a b L R ha ha2 hab hL hR hLip hWbound hMass
  refine ⟨|X.drift| * A + M + |q| * R, ?_, ?_⟩
  · positivity
  intro y hy
  have hD : |X.drift * deriv w y| ≤ |X.drift| * A := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hDeriv y hy) (abs_nonneg _)
  have hW : |q * w y| ≤ |q| * R := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hWbound y hy.2) (abs_nonneg _)
  have htri :
      |X.drift * deriv w y +
        (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) - q * w y| ≤
      (|X.drift * deriv w y| +
        |∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν|) +
        |q * w y| := by
    calc
      _ ≤ |X.drift * deriv w y +
          (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν)| +
          |q * w y| := by
        simpa [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (X.drift * deriv w y +
            (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν))
            0 (q * w y))
      _ ≤ (|X.drift * deriv w y| +
          |∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν|) +
          |q * w y| := by
        have hleft :
            |X.drift * deriv w y +
              (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν)| ≤
            |X.drift * deriv w y| +
              |∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν| :=
          abs_add_le _ _
        linarith only [hleft]
  linarith [htri, hD, hJ y hy, hW]
