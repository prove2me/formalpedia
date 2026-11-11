-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise33_original_smallband_compensator_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T17:48:29.108501+00:00
-- url     : https://prove2.me/submissions/e46f2084-2bdc-4c37-b65e-55b6293251c3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The finite-band compensator is the difference of two adapted original residuals. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) (t : ℝ≥0) :
    Measurable[𝓕 t]
      (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) := by
  classical
  have hZero (ω : Ω) :
      avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω = 0 := by
    simp [avram_p4_h_gaussian_intrinsic_small_band_compensated]
  have hEq :
      (fun ω : Ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) =
        (fun ω : Ω =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) := by
    funext ω
    unfold avram_p4_h_gaussian_intrinsic_truncated_residual
    rw [hZero ω]
    ring
  rw [hEq]
  exact
    (avram_mix_gauss14_original_intrinsic_truncated_residual_adapted X 0 t).sub
      (avram_mix_gauss14_original_intrinsic_truncated_residual_adapted X n t)
