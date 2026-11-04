-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_max_HJB_exact_physical_generator_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:31:11.726121+00:00
-- url     : https://prove2.me/submissions/368756aa-53ac-429e-9730-ce7659048ece

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The true original BV generator representation converts the source maximum HJB into a nonpositive physical generator on the positive capped region. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [SFinite P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
  (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.GeneratorIntegrable w y ∧
    max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
  ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.drift * deriv w y +
      (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) -
      q * w y ≤ 0 := by
  intro y hy hcap
  have hSource := hw_hjb y hy hcap
  have hPhysical :=
    boundedVariation_generator_physical_drift_representation
      X hBV w y hSource.1
  have hle : X.generator w y - q * w y ≤ 0 :=
    (le_max_left _ _).trans (le_of_eq hSource.2)
  rw [hPhysical] at hle
  exact hle
