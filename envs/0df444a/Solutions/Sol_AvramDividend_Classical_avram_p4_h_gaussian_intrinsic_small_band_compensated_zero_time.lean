-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:44:37.350075+00:00
-- url     : https://prove2.me/submissions/192e6a3b-9bd6-40ab-8fab-606805ec5f47

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The actual intrinsic compensated finite-band jump process vanishes at time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) (ω : Ω) :
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n 0 ω = 0 := by
  simp [avram_p4_h_gaussian_intrinsic_small_band_compensated]
