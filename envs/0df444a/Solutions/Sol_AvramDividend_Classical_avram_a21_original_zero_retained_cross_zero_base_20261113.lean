-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_zero_retained_cross_zero_base_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:38:40.797822+00:00
-- url     : https://prove2.me/submissions/163670d9-02cc-44b6-8e3d-0b8c61547752

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original physical retained compensated jump band vanishes at index zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) :
    Integrable (fun ω =>
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω *
        avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) P ∧
    (∫ ω,
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω *
        avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω ∂P) = 0 := by
  simp [avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff]
