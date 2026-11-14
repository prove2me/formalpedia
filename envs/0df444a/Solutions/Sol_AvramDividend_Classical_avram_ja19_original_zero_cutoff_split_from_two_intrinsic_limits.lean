-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja19_original_zero_cutoff_split_from_two_intrinsic_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:24:59.397968+00:00
-- url     : https://prove2.me/submissions/cf16bad0-9760-46e1-a3a0-44dbcab3ea50

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_cutoff_residual_gaussian_core_split
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Both intrinsic limits refer to the same original source and together recover the zero-cutoff source exactly. -/
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
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω =
        R t ω + Jsmall t ω := by
  filter_upwards [hR, hJ] with ω hRω hJω
  intro t
  have hSplit (k : ℕ) :
      avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω +
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω =
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω := by
    rw [avram_ja21_original_cutoff_residual_gaussian_core_split]
    rw [avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff]
    ring
  have hLimit :
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω +
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (R t ω + Jsmall t ω)) :=
    (hRω t).add (hJω t)
  have hConstant :
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω +
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω)) := by
    simp_rw [hSplit]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hConstant hLimit
