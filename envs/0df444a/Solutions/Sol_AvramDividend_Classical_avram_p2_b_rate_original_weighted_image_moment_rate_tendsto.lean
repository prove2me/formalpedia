-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_moment_rate_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:20:43.553443+00:00
-- url     : https://prove2.me/submissions/caf4e46f-359d-4e0a-9f6e-430d83df82ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_fourth_weighted_integer_moments
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_integer_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_exponential_image_moment_integral_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : ∀ t : ℝ≥0, Measurable (X.X t))
    (k : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    Tendsto
      (fun h : ℝ =>
        ((∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
          ((P.withDensity (fun ω =>
            ENNReal.ofReal ((Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (θ * X.X (Real.toNNReal h) ω)))).toReal / h))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ y in Iio (0 : ℝ), (Real.exp (θ * y)) ^ k *
        (Real.exp (θ * y) - 1) ^ 4 ∂X.ν)) := by
  have hEq (h : ℝ) :
      (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
        ((P.withDensity (fun ω =>
          ENNReal.ofReal ((Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
          (fun ω => Real.exp (θ * X.X (Real.toNNReal h) ω)))).toReal =
      (∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω)) ^ k *
        (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) := by
    have hi :=
      AvramDividend.Classical.avram_p2_b_rate_original_weighted_integer_integrable
        X (Real.toNNReal h) k θ hθ
    rw [AvramDividend.Classical.avram_p2_b_rate_weighted_exponential_image_moment_integral_eq
      P (X.X (Real.toNNReal h)) (hX _) θ k hi]
    exact ENNReal.toReal_ofReal (integral_nonneg (fun ω => by positivity))
  have hFun :
      (fun h : ℝ =>
        ((∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
          ((P.withDensity (fun ω =>
            ENNReal.ofReal ((Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (θ * X.X (Real.toNNReal h) ω)))).toReal / h)) =
      (fun h : ℝ =>
        (∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω)) ^ k *
          (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h) := by
    funext h
    rw [hEq h]
  rw [hFun]
  exact AvramDividend.Classical.avram_p2_b_rate_original_fourth_weighted_integer_moments
    X k θ hθ
