-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf15_intrinsic_gaussian_cutoff_residual_zero_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T14:02:39.522694+00:00
-- url     : https://prove2.me/submissions/b131d6f3-b918-49b5-a420-124e52a6c5a0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- Every physical intrinsic Gaussian cutoff residual vanishes at initial time, without finite activity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) (ω : Ω) :
    avram_p4_h_gaussian_intrinsic_truncated_residual X n (0 : ℝ≥0) ω = 0 := by
  simp [avram_p4_h_gaussian_intrinsic_truncated_residual,
    avram_p4_h_gaussian_intrinsic_small_band_compensated,
    avram_p4_h_gaussian_intrinsic_large_jump_sum,
    X.X_zero ω]
