-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_any_activity_intrinsic_gaussian_source_zero_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:41:06.810664+00:00
-- url     : https://prove2.me/submissions/f9617266-50e4-4084-8f1c-b202c19d5858

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_intrinsic_gaussian_cutoff_residual_zero_origin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω))) :
    ∀ᵐ ω ∂P, R 0 ω = 0 := by
  filter_upwards [hR] with ω hω
  have hCutZero :
      (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k 0 ω) =
        fun _ => (0 : ℝ) := by
    funext k
    exact avram_mix_inf15_intrinsic_gaussian_cutoff_residual_zero_origin X k ω
  have hLim : Tendsto (fun k : ℕ =>
      avram_p4_h_gaussian_intrinsic_truncated_residual X k 0 ω)
      atTop (nhds (0 : ℝ)) := by
    simpa only [hCutZero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  exact (tendsto_nhds_unique hLim (hω 0)).symm
