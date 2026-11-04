-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_levy_measure_eq_negative_restrict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:36:04.177391+00:00
-- url     : https://prove2.me/submissions/edaf0c68-df9a-4096-b1de-2b125f15793e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original Levy measure itself is carried by strictly negative marks
as an exact equality of measures on all Borel sets. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    X.ν = X.ν.restrict (Iio (0 : ℝ)) := by
  apply Measure.ext
  intro B hB
  calc
    X.ν B = X.ν (B ∩ Iio (0 : ℝ)) :=
      avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction
        X B hB
    _ = (X.ν.restrict (Iio (0 : ℝ))) B :=
      (Measure.restrict_apply hB).symm
