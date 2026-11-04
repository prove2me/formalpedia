-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_max_HJB_to_physical_generator_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:25:04.688301+00:00
-- url     : https://prove2.me/submissions/ff4c0f32-9a6b-4af2-89ea-5703f165efd8

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Under the true original BV generator formula, the maximum-form HJB condition yields nonpositive physical drift for positive capital below C. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [SFinite P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
  (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.GeneratorIntegrable w y ∧
    max (X.generator w y - q * w y) (1 - deriv w y) = 0)
  (hPhysical : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.generator w y =
      X.drift * deriv w y +
        (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν)) :
  ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.drift * deriv w y +
      (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) -
      q * w y ≤ 0 := by
  intro y hy hcap
  have hmax := (hw_hjb y hy hcap).2
  have hle : X.generator w y - q * w y ≤ 0 :=
    (le_max_left _ _).trans (le_of_eq hmax)
  rw [hPhysical y hy hcap] at hle
  exact hle
