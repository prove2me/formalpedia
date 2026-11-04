-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_physical_HJB_interior_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:37:40.479208+00:00
-- url     : https://prove2.me/submissions/b3ab1de6-8ce8-4e10-8895-e614c062b5f8

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_generator_physical_drift_interval_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Translate the original BV interior generator HJB inequality into its
physical drift and negative-jump integral form without dropping a residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (y : ℝ)
    (hy : 0 < y) (hyC : ENNReal.ofReal y < C)
    (hgen : X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0) :
    X.drift * deriv w y +
        (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) -
      q * w y ≤ 0 := by
  obtain ⟨hphysical, _⟩ :=
    avram_p3_a_bvdrift_original_generator_physical_drift_interval_budget
      X hBV w y hgen.1
  rw [← hphysical]
  exact hgen.2
