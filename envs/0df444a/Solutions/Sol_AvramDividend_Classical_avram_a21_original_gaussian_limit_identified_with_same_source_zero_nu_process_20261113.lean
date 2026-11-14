-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_gaussian_limit_identified_with_same_source_zero_nu_process_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:45:40.673336+00:00
-- url     : https://prove2.me/submissions/1bfa7b9f-566f-43dd-8c54-42211cde7531

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The physical cutoff limit agrees almost surely with the source Gaussian companion. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (Jsmall : ℝ≥0 → Ω → ℝ) (R : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0)
    (hJsource : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω)))
    (hRsource : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hDecomp : ∀ᵐ ω ∂P,
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω =
          (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω) :
    ∀ᵐ ω ∂P, R t ω = Y.X t ω - (t : ℝ) * Y.c := by
  filter_upwards [hJsource, hRsource, hDecomp] with ω hJ hR hDec
  have hPath :
      (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω) =
      (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω) := by
    funext k
    exact avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
      X k t ω
  rw [hPath] at hR
  have hLimit :
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop
        (nhds (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω -
          Jsmall t ω)) := tendsto_const_nhds.sub hJ
  have hUniq := tendsto_nhds_unique hR hLimit
  rw [hDec] at hUniq
  linarith
