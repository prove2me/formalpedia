-- Prove2me | solution 1 for AvramDividend.Classical.avram_a76_finite_negative_activity_levy_gaussian_jump_exponent_split_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:16:24.395236+00:00
-- url     : https://prove2.me/submissions/fa92de1c-50ee-498f-a341-6a1c7dafd240

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a74_negative_levy_compensated_exponential_integral_split_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a75_finite_negative_activity_exponential_compensator_integrable_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Decompose the original finite-activity Levy exponent without a bounded-variation hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    X.ψ θ =
      X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
        (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν) -
        θ * (∫ y in Ioo (-1 : ℝ) 0, y ∂X.ν) := by
  have hFiniteLt : X.ν (Iio (0 : ℝ)) < ⊤ :=
    lt_top_iff_ne_top.mpr hFinite
  obtain ⟨hExp, hComp⟩ :=
    avram_a75_finite_negative_activity_exponential_compensator_integrable_20261114
      X.ν hFiniteLt θ hθ
  have hSplit :=
    avram_a74_negative_levy_compensated_exponential_integral_split_20261114
      X.ν θ hExp hComp
  change X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
    (∫ y in Iio (0 : ℝ),
      Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y ∂X.ν) =
    X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
      (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν) -
      θ * (∫ y in Ioo (-1 : ℝ) 0, y ∂X.ν)
  rw [hSplit]
  ring
