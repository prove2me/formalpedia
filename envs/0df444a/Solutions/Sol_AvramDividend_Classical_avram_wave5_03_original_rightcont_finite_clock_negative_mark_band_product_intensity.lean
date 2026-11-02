-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_rightcont_finite_clock_negative_mark_band_product_intensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:36:14.963318+00:00
-- url     : https://prove2.me/submissions/a0ddbd66-3824-4db4-a954-e47cbe40c441

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_levy_intensity_sigmafinite_from_process_fields
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original Lévy intensity has finite product mass on any finite mark band under a finite source predictable clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμfinite : μ Set.univ < ∞)
    (B : Set ℝ) (hBfinite : (X.ν.restrict (Iio (0 : ℝ))) B < ∞) :
    (@Measure.prod (ℝ≥0 × Ω) ℝ
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)
      μ (X.ν.restrict (Iio (0 : ℝ))))
        ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B) < ∞ := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : SigmaFinite X.ν :=
    avram_wave5_01_actual_source_levy_intensity_sigmafinite_from_process_fields X
  change (μ.prod (X.ν.restrict (Iio (0 : ℝ))))
    ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B) < ∞
  rw [Measure.prod_prod]
  exact ENNReal.mul_lt_top hμfinite hBfinite
