-- Prove2me | solution 1 for AvramDividend.Classical.bv_lk_algebra_of_exponent_and_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T11:52:13.690309+00:00
-- url     : https://prove2.me/submissions/e141261c-f99e-4a66-b804-cc6e5c0b48ee

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution (ν : Measure ℝ) (θ δ ψ : ℝ)
    (hcore : ψ = δ * θ +
      ∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ∂ν)
    (hmap :
      (∫ z : ℝ≥0, (1 - Real.exp (-θ * (z : ℝ)))
        ∂(ν.map (fun y : ℝ => Real.toNNReal (-y)))) =
      ∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂ν) :
    ψ = δ * θ -
      ∫ z : ℝ≥0, (1 - Real.exp (-θ * (z : ℝ)))
        ∂(ν.map (fun y : ℝ => Real.toNNReal (-y))) := by
  have hint :
      (∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ∂ν) =
      -(∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂ν) := by
    calc
      (∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ∂ν) =
        ∫ y in Iio (0 : ℝ), (-(1 - Real.exp (θ * y))) ∂ν := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun y : ℝ => by ring)
      _ = -(∫ y in Iio (0 : ℝ),
          (1 - Real.exp (θ * y)) ∂ν) := by simp only [integral_neg]
  calc
    ψ = δ * θ + (∫ y in Iio (0 : ℝ),
      (Real.exp (θ * y) - 1) ∂ν) := hcore
    _ = δ * θ - (∫ y in Iio (0 : ℝ),
      (1 - Real.exp (θ * y)) ∂ν) := by rw [hint]; ring
    _ = δ * θ -
      (∫ z : ℝ≥0, (1 - Real.exp (-θ * (z : ℝ)))
        ∂(ν.map (fun y : ℝ => Real.toNNReal (-y)))) := by rw [hmap]
