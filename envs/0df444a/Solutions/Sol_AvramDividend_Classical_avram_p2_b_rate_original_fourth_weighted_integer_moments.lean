-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_fourth_weighted_integer_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:37:35.690202+00:00
-- url     : https://prove2.me/submissions/0cac86d2-1243-4814-8dc2-58bd0c583940

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
    (k : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    Tendsto
      (fun h : ℝ =>
        (∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω)) ^ k *
          (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ y in Iio (0 : ℝ), (Real.exp (θ * y)) ^ k *
        (Real.exp (θ * y) - 1) ^ 4 ∂X.ν)) := by
  have hρ : 0 ≤ (k : ℝ) * θ :=
    mul_nonneg (Nat.cast_nonneg k) hθ
  have hh :=
    AvramDividend.Classical.avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative
      X ((k : ℝ) * θ) θ hρ hθ
  have hexp (y : ℝ) :
      Real.exp (((k : ℝ) * θ) * y) = (Real.exp (θ * y)) ^ k := by
    calc
      Real.exp (((k : ℝ) * θ) * y) =
          Real.exp ((k : ℝ) * (θ * y)) := by ring
      _ = (Real.exp (θ * y)) ^ k := by
        simpa using (Real.exp_nat_mul (θ * y) k)
  simpa only [hexp] using hh