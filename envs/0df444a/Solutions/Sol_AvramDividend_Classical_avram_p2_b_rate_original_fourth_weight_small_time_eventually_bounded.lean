-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_fourth_weight_small_time_eventually_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:38:41.177288+00:00
-- url     : https://prove2.me/submissions/f07ee643-ef3c-4ddf-a30f-1f194820dc9a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ((∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h) <
        (∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1 := by
  have hs :=
    AvramDividend.Classical.avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative
      X 0 θ (le_refl (0 : ℝ)) hθ
  let L : ℝ :=
    ∫ y in Iio (0 : ℝ), Real.exp ((0 : ℝ) * y) *
      (Real.exp (θ * y) - 1) ^ 4 ∂X.ν
  have hb : ∀ᶠ z : ℝ in nhds L, z < L + 1 :=
    eventually_lt_nhds (by dsimp [L]; linarith)
  simpa only [L, zero_mul, Real.exp_zero, one_mul] using hs.eventually hb