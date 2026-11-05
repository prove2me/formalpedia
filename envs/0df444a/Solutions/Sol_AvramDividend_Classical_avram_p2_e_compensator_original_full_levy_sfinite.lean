-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_full_levy_sfinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:06:52.510384+00:00
-- url     : https://prove2.me/submissions/ceaddec1-fa2b-467f-92d3-9a83a347c716

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The entire original source Levy measure is s-finite from negative support and its negative restriction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    SFinite X.ν := by
  have hνrestrict : X.ν.restrict (Iio (0 : ℝ)) = X.ν := by
    ext A hA
    rw [Measure.restrict_apply hA]
    exact
      (avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction
        X A hA).symm
  simpa only [hνrestrict] using (levy_negative_jump_measure_sFinite X)

