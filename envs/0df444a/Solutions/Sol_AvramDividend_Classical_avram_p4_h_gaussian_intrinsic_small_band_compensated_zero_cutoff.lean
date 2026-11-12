-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:56:53.973158+00:00
-- url     : https://prove2.me/submissions/db9aed94-a337-4a25-ad8d-cecbecb35fe3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- At the zeroth cutoff the original negative small-jump band is empty,
so both the intrinsic marked-jump integral and the source ν drift vanish. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (ω : Ω) :
    avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω = 0 := by
  simp [avram_p4_h_gaussian_intrinsic_small_band_compensated]
