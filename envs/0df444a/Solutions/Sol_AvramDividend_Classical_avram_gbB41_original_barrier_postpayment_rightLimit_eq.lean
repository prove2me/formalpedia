-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB41_original_barrier_postpayment_rightLimit_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T15:56:05.633819+00:00
-- url     : https://prove2.me/submissions/5f5e5089-afe9-4315-8b19-bb56da9267fa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous
import Theorems.Thm_AvramDividend_Classical_rightLimit_eq_of_monotone_right_continuous
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The source barrier has no right-hand dividend jump at any physical time. -/
theorem solution
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ)
  (ω : Ω) (t : ℝ≥0) :
  rightLimit (barrierStrategy X c c) t ω =
    barrierStrategy X c c t ω := by
  exact rightLimit_eq_of_monotone_right_continuous
    (barrierStrategy X c c) ω t
    (barrierStrategy_monotone X c ω)
    (barrierStrategy_right_continuous X c ω t)
