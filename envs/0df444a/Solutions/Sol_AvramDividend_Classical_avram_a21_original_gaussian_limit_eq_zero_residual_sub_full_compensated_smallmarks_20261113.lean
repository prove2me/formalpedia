-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_gaussian_limit_eq_zero_residual_sub_full_compensated_smallmarks_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:51:17.651508+00:00
-- url     : https://prove2.me/submissions/2e0a15fc-d60b-436b-96cc-5ac59ac07f91

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

/-- Physical Gaussian cutoff limit equals R0 minus the full compensated small-mark field. -/
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
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      R t ω =
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω -
          Jsmall t ω := by
  filter_upwards [hJ, hR] with ω hJω hRω
  intro t
  have hPath :
      (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω) =
      (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω) := by
    funext k
    exact avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
      X k t ω
  have hRt := hRω t
  rw [hPath] at hRt
  have hLimit : Tendsto (fun k : ℕ =>
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
      atTop (nhds (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω -
        Jsmall t ω)) := tendsto_const_nhds.sub (hJω t)
  exact tendsto_nhds_unique hRt hLimit
