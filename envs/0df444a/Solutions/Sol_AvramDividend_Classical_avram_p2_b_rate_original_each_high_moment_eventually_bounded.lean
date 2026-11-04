-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_each_high_moment_eventually_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:59:27.34482+00:00
-- url     : https://prove2.me/submissions/ca329994-4b05-4f1d-a4e0-337e2bf89e12

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_fourth_weighted_integer_moments

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ((∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω)) ^ k *
        (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h) <
        (∫ y in Iio (0 : ℝ), (Real.exp (θ * y)) ^ k *
          (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1 := by
  have hs :=
    AvramDividend.Classical.avram_p2_b_rate_original_fourth_weighted_integer_moments
      X k θ hθ
  let L : ℝ :=
    ∫ y in Iio (0 : ℝ), (Real.exp (θ * y)) ^ k *
      (Real.exp (θ * y) - 1) ^ 4 ∂X.ν
  have hb : ∀ᶠ z : ℝ in nhds L, z < L + 1 :=
    eventually_lt_nhds (by dsimp [L]; linarith)
  simpa only [L] using hs.eventually hb
