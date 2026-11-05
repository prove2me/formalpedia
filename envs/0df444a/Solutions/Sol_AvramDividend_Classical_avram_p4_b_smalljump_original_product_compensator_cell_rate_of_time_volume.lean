-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_product_compensator_cell_rate_of_time_volume
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:55:24.029968+00:00
-- url     : https://prove2.me/submissions/300cd06b-6098-49e9-9f03-363e4bf59419

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual Lévy source measure is s-finite, and its product compensator has exact cell mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (timeMeasure : Measure ℝ≥0) (s t : ℝ≥0) (B : Set ℝ)
    (hTimeVolume : timeMeasure (Ioc s t) =
      ((t - s : ℝ≥0) : ℝ≥0∞)) :
    (timeMeasure.prod X.ν) (Ioc s t ×ˢ B) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  have hνrestrict : X.ν.restrict (Iio (0 : ℝ)) = X.ν := by
    ext A hA
    rw [Measure.restrict_apply hA]
    exact
      (avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction
        X A hA).symm
  have hSFinite : SFinite X.ν := by
    simpa only [hνrestrict] using (levy_negative_jump_measure_sFinite X)
  letI : SFinite X.ν := hSFinite
  calc
    (timeMeasure.prod X.ν) (Ioc s t ×ˢ B)
        = timeMeasure (Ioc s t) * X.ν B :=
          Measure.prod_prod (Ioc s t) B
    _ = ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
          rw [hTimeVolume]

