-- Prove2me | solution 1 for AvramDividend.Classical.bv_laplace_exponent_positive_magnitude_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T11:15:21.728862+00:00
-- url     : https://prove2.me/submissions/94640e0f-35bf-475c-a149-c2fc6352cce7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_rearrangement_of_integrable
import Theorems.Thm_AvramDividend_Classical_negative_jump_magnitude_integral_transform
import Theorems.Thm_AvramDividend_Classical_bv_compensation_integrable
import Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation) (θ : ℝ) (hθ : 1 ≤ θ) :
    X.ψ θ = X.drift * θ -
      ∫ z : ℝ≥0, (1 - Real.exp (-θ * (z : ℝ)))
        ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))) := by
  have hexp := bv_exponential_jump_integrable X hbv θ hθ
  have hcomp := bv_compensation_integrable X hbv θ
  have hcore :=
    bv_laplace_exponent_rearrangement_of_integrable X hbv θ hexp hcomp
  have hsign (y : ℝ) :
      Real.exp (θ * y) - 1 = -(1 - Real.exp (θ * y)) := by
    ring
  calc
    X.ψ θ = X.drift * θ +
        (∫ y in Iio (0 : ℝ),
          (Real.exp (θ * y) - 1) ∂X.ν) := hcore
    _ = X.drift * θ -
        (∫ y in Iio (0 : ℝ),
          (1 - Real.exp (θ * y)) ∂X.ν) := by
      simp_rw [hsign, integral_neg]
      ring
    _ = X.drift * θ -
        (∫ z : ℝ≥0, (1 - Real.exp (-θ * (z : ℝ)))
          ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) := by
      rw [negative_jump_magnitude_integral_transform X.ν θ]
