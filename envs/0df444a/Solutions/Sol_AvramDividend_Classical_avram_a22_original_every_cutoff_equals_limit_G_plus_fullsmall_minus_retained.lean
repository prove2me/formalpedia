-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_every_cutoff_equals_limit_G_plus_fullsmall_minus_retained
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T13:00:58.097201+00:00
-- url     : https://prove2.me/submissions/5cb6e191-1332-4298-a952-e38724ba32ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja19_original_zero_cutoff_split_from_two_intrinsic_limits
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- All original physical cutoff residuals share one Gaussian source and one compensated small-mark process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℝ≥0),
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω =
        R t ω + Jsmall t ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω := by
  have hSplit :=
    avram_ja19_original_zero_cutoff_split_from_two_intrinsic_limits
      X R Jsmall hR hJ
  filter_upwards [hSplit] with ω hω
  intro n t
  have hCut :=
    avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
      X n t ω
  rw [hCut, hω t]
