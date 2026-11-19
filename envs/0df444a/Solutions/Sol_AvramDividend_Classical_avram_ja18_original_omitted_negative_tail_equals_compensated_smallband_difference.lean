-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_omitted_negative_tail_equals_compensated_smallband_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:22:19.863817+00:00
-- url     : https://prove2.me/submissions/e880cf56-009d-4dab-b04f-16869cd27e43

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_eq_zero_residual_sub_full_compensated_smallmarks_20261113
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_cutoff_residual_gaussian_core_split
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original intrinsic omitted jump tail is precisely its finite-cutoff residual error. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω =
        Jsmall t ω - avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω := by
  have hlim :=
    avram_a21_original_gaussian_limit_eq_zero_residual_sub_full_compensated_smallmarks_20261113
      X Jsmall R hJ hR
  filter_upwards [hlim] with ω hω
  intro n t
  rw [avram_ja21_original_cutoff_residual_gaussian_core_split X n t ω, hω t,
    avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff X t ω]
  ring
