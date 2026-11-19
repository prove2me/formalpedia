-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_full_compensated_jump_equals_smalllarge_and_drift_adjustment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:45:35.409895+00:00
-- url     : https://prove2.me/submissions/096b1afa-bde4-401c-9a3a-7ea6ca80aaea

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_intrinsic_gaussian_smallmark_largemark_full_path_ae_split
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The full compensated jump component includes the uncompensated large negative marks. -/
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
        atTop (nhds (Jsmall t ω)))
    (μ : ℝ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω - (t : ℝ) * μ - R t ω =
        Jsmall t ω + avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
        (t : ℝ) * (X.c - μ) := by
  have hSource :=
    avram_ja18_original_intrinsic_gaussian_smallmark_largemark_full_path_ae_split
      X R Jsmall hR hJ
  filter_upwards [hSource] with ω hω
  intro t
  have hh := hω t
  linarith
