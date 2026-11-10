-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T01:05:42.197724+00:00
-- url     : https://prove2.me/submissions/d55c8dd3-790f-455c-9ca2-fc1b179c5481

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- All original-path terms common to two cutoffs cancel identically. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n m : ℕ) (t : ℝ≥0) (ω : Ω) :
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
      avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω =
    avram_p4_h_gaussian_intrinsic_small_band_compensated X m t ω -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω := by
  simp only [avram_p4_h_gaussian_intrinsic_truncated_residual]
  ring
