-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_gaussian_limit_omitted_tail_zero_time_cross_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:29:22.017183+00:00
-- url     : https://prove2.me/submissions/5a14b47e-47f9-4ca0-b47c-aee5314905f3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin18_original_intrinsic_gaussian_residual_zero_time_public
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original Gaussian residual limit is orthogonal to any omitted tail at time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ n : ℕ,
      (∫ ω, R 0 ω *
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n 0 ω - R 0 ω) ∂P) = 0 := by
  intro n
  have hZero : ∀ᵐ ω ∂P, R 0 ω = 0 :=
    avram_mix_fin18_original_intrinsic_gaussian_residual_zero_time_public X R hR
  apply integral_eq_zero_of_ae
  filter_upwards [hZero] with ω hω
  simp [hω]
