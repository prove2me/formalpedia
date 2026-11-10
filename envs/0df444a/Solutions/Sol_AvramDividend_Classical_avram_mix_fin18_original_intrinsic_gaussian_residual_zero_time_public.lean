-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin18_original_intrinsic_gaussian_residual_zero_time_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T13:57:52.652417+00:00
-- url     : https://prove2.me/submissions/1064d3e2-fd05-450f-aed5-a63963b80965

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω))) :
    ∀ᵐ ω ∂P, R 0 ω = 0 := by
  filter_upwards [hRsource] with ω hω
  have hcut : ∀ k : ℕ,
      avram_p4_h_gaussian_intrinsic_truncated_residual X k 0 ω = 0 := by
    intro k
    simp [avram_p4_h_gaussian_intrinsic_truncated_residual,
      X.X_zero ω,
      avram_p4_h_gaussian_intrinsic_small_band_compensated,
      avram_p4_h_gaussian_intrinsic_large_jump_sum]
  have hzero :
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k 0 ω)
        atTop (nhds (0 : ℝ)) := by
    simpa only [hcut] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  exact tendsto_nhds_unique (hω 0) hzero
