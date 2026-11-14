-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:57:58.559207+00:00
-- url     : https://prove2.me/submissions/f25b2af4-9c9d-4cd1-8dbc-762e89d93a35

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_cutoff_residual_gaussian_core_split
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Physical original cutoff residual equals the zero cutoff residual
minus the exactly retained compensated source negative jump strip. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω =
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω := by
  simpa only [avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff,
    add_zero] using
    (avram_ja21_original_cutoff_residual_gaussian_core_split X n t ω)
