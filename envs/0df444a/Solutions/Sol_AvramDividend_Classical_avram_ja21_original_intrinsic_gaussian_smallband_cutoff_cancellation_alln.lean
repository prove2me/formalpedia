-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja21_original_intrinsic_gaussian_smallband_cutoff_cancellation_alln
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T14:34:21.159514+00:00
-- url     : https://prove2.me/submissions/4b1e0c31-83ec-458c-9491-50ca28587797

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (t : ℝ≥0) (ω : Ω) :
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω +
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω =
    X.X t ω - (t : ℝ) * X.c -
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω := by
  unfold avram_p4_h_gaussian_intrinsic_truncated_residual
  ring
