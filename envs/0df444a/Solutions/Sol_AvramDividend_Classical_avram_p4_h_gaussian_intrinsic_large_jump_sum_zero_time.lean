-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_intrinsic_large_jump_sum_zero_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:48:55.928199+00:00
-- url     : https://prove2.me/submissions/b8707493-0d2e-4b9f-a1cc-89e55a19aeb9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The actual original source large-jump integral vanishes at time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    avram_p4_h_gaussian_intrinsic_large_jump_sum X 0 ω = 0 := by
  simp [avram_p4_h_gaussian_intrinsic_large_jump_sum]
