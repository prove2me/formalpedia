-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_normalised_negative_mark_laplace_and_rate_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:46:38.52152+00:00
-- url     : https://prove2.me/submissions/daaac89a-0dd0-4a88-beaa-ca542aa5a758

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_nonzero_negative_mark_rate_real_positive_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_negative_mark_exponential_mass_between_zero_and_rate_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_finite_negative_mark_exponential_integrable_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_finite_mark_exponential_excess_integral_split_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The single physical negative mark Laplace moment has correct normalized intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hNu : X.ν ≠ 0)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧
      (X.ν (Iio (0 : ℝ))).toReal * (m - 1) =
        (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 ∂X.ν) := by
  classical
  let rateMass : ℝ := (X.ν (Iio (0 : ℝ))).toReal
  let a : ℝ :=
    ∫ y in Iio (0 : ℝ), Real.exp (θ * y) ∂X.ν
  have hFiniteLt : X.ν (Iio (0 : ℝ)) < ⊤ :=
    lt_top_iff_ne_top.mpr hFinite
  have hrateMass : 0 < rateMass :=
    avram_a27_original_nonzero_negative_mark_rate_real_positive_20261117
      X hFinite hNu
  have haBounds : 0 ≤ a ∧ a ≤ rateMass :=
    avram_a27_original_negative_mark_exponential_mass_between_zero_and_rate_20261117
      X.ν hFiniteLt θ hθ
  have haInt : IntegrableOn
      (fun y : ℝ => Real.exp (θ * y)) (Iio (0 : ℝ)) X.ν :=
    avram_a27_finite_negative_mark_exponential_integrable_20261117
      X.ν hFiniteLt θ hθ
  let μ : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  haveI : IsFiniteMeasure μ := ⟨by simpa [μ] using hFiniteLt⟩
  have hSplit :
      (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν) =
        a - rateMass := by
    have hMarkSplit :=
      avram_a27_finite_mark_exponential_excess_integral_split_20261117
        μ θ haInt
    simpa [a, rateMass, μ, measureReal_def] using hMarkSplit
  refine ⟨a / rateMass, ?_, ?_, ?_⟩
  · exact div_nonneg haBounds.1 (le_of_lt hrateMass)
  · apply (div_le_iff₀ hrateMass).2
    simpa using haBounds.2
  · change rateMass * (a / rateMass - 1) = _
    rw [hSplit]
    field_simp
