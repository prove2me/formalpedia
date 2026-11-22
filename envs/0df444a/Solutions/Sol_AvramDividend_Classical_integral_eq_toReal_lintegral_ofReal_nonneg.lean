-- Prove2me | solution 1 for AvramDividend.Classical.integral_eq_toReal_lintegral_ofReal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T07:48:16.713893+00:00
-- url     : https://prove2.me/submissions/fbfde551-d96c-46c5-8937-6e5dcb9349eb

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution (ν : Measure ℝ) (f : ℝ → ℝ)
    (hf : Integrable f ν) (hpos : ∀ᵐ y ∂ν, 0 ≤ f y) :
    (∫ y : ℝ, f y ∂ν) =
      (∫⁻ y : ℝ, ENNReal.ofReal (f y) ∂ν).toReal := by
  have hn : 0 ≤ (∫ y : ℝ, f y ∂ν) := integral_nonneg_of_ae hpos
  have h := ofReal_integral_eq_lintegral_ofReal hf hpos
  calc
    (∫ y : ℝ, f y ∂ν) =
        (ENNReal.ofReal (∫ y : ℝ, f y ∂ν)).toReal :=
          (ENNReal.toReal_ofReal hn).symm
    _ = (∫⁻ y : ℝ, ENNReal.ofReal (f y) ∂ν).toReal :=
      congrArg ENNReal.toReal h
