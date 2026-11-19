-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_ruinclipped_stopped_reserve_full_threechannel_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:43:33.189916+00:00
-- url     : https://prove2.me/submissions/ec6d036e-b43c-4648-b3a0-160d378f99d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_stopped_W_sameX_intrinsic_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_eq_zero_residual_sub_full_compensated_smallmarks_20261113
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original stopped reserve retains the uncompensated large negative jumps exactly. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω))) :
    ∀ᵐ ω ∂P, W ω =
      x + (τ ω : ℝ) * X.c + R (τ ω) ω + Jsmall (τ ω) ω +
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ ω) ω -
      (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
       then rightLimit D (τ ω) ω else D (τ ω) ω) := by
  have hlim :=
    avram_a21_original_gaussian_limit_eq_zero_residual_sub_full_compensated_smallmarks_20261113
      X Jsmall R hJ hR
  filter_upwards [hlim] with ω hω
  have hLedger :=
    avram_p4_f3_original_stopped_W_sameX_intrinsic_residual X x D 0 τ W hW ω
  have hSource := hω (τ ω)
  have hz :=
    avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff X (τ ω) ω
  simp only [hz] at hLedger
  linarith
