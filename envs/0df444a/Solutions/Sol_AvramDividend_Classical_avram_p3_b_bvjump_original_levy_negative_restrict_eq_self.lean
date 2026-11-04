-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_levy_negative_restrict_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:53:30.444527+00:00
-- url     : https://prove2.me/submissions/03057fa9-4033-4e00-a638-c59416ea101a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    X.ν.restrict (Iio (0 : ℝ)) = X.ν := by
  ext B hB
  rw [Measure.restrict_apply hB]
  exact (avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction
    X B hB).symm
