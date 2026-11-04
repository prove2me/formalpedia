-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_rescaled_weighted_signed_moment_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:07:31.559691+00:00
-- url     : https://prove2.me/submissions/3f15e799-f600-4742-98a8-8a557d8b8d81

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_rescaled_weighted_exp_real_moments_converge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Finite signed linear combinations of the original rescaled real
weighted-image polynomial moments converge to the genuine Levy moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (s : Finset ℕ) (a : ℕ → ℝ) :
    Tendsto
      (fun h : ℝ => ∑ k ∈ s, a k * ((ENNReal.ofReal h)⁻¹ *
          (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
            ((P.withDensity (fun ω => ENNReal.ofReal
              ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
              (fun ω => Real.exp (X.X (Real.toNNReal h) ω))))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∑ k ∈ s, a k * ((∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
          (((X.ν.restrict (Iio (0 : ℝ))).withDensity
            (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
            Real.exp)).toReal))) := by
  apply tendsto_finset_sum
  intro k hk
  exact (avram_p2_original_rescaled_weighted_exp_real_moments_converge X k).const_mul (a k)
