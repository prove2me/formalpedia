-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_each_high_moment_eventually_zero_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:11:12.148482+00:00
-- url     : https://prove2.me/submissions/b02a5ef6-ffa9-4221-b26e-44d284114e02

import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_each_high_moment_eventually_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_levy_weighted_moment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_weighted_all_moments_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_weighted_integral_moment_le_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (k : ℕ) :
    ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω)) ^ k *
        (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h <
      (∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1 := by
  have hzero : IntegrableOn
      (fun y : ℝ => (Real.exp (θ * y) - 1) ^ 4) (Iio (0 : ℝ)) X.ν := by
    simpa using
      AvramDividend.Classical.avram_p2_b_rate_original_levy_weighted_moment_integrable
        X 0 θ le_rfl hθ
  have hk :=
    AvramDividend.Classical.avram_p2_b_rate_negative_weighted_all_moments_integrable
      X.ν θ hθ k hzero
  have hdom :=
    AvramDividend.Classical.avram_p2_b_rate_negative_weighted_integral_moment_le_zero
      X.ν θ hθ k hzero hk
  have hlim :=
    AvramDividend.Classical.avram_p2_b_rate_original_each_high_moment_eventually_bounded
      X k θ hθ
  filter_upwards [hlim] with h hh
  linarith [hdom]
