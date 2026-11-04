-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_fourth_weighted_finite_polynomial_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:47:41.286877+00:00
-- url     : https://prove2.me/submissions/4f49571a-35c6-40eb-8628-a316a29b00cd

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
    (s : Finset ℕ) (a : ℕ → ℝ) (θ : ℝ) (hθ : 0 ≤ θ) :
    Tendsto
      (fun h : ℝ => ∑ k ∈ s,
        a k * ((∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω)) ^ k *
          (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∑ k ∈ s, a k *
        (∫ y in Iio (0 : ℝ), (Real.exp (θ * y)) ^ k *
          (Real.exp (θ * y) - 1) ^ 4 ∂X.ν))) := by
  refine tendsto_finset_sum s (fun k hk => ?_)
  exact Filter.Tendsto.const_mul (a k)
    (AvramDividend.Classical.avram_p2_b_rate_original_fourth_weighted_integer_moments
      X k θ hθ)
