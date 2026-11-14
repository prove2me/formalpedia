-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_cutoff_residual_eq_gaussian_limit_plus_omitted_negative_tail_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:52:14.822725+00:00
-- url     : https://prove2.me/submissions/f88b7c21-380f-41f0-adef-af1534d5f152

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_eq_zero_residual_sub_full_compensated_smallmarks_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The true original physical finite cutoff is Gaussian limit plus omitted jump tail. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Jsmall R : ℝ≥0 → Ω → ℝ)
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω)))
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω))) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω =
        R t ω + (Jsmall t ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) := by
  have hLimit :=
    avram_a21_original_gaussian_limit_eq_zero_residual_sub_full_compensated_smallmarks_20261113
      X Jsmall R hJ hR
  filter_upwards [hLimit] with ω hω
  intro n t
  have hSplit :=
    avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
      X n t ω
  have hIdentification := hω t
  linarith
