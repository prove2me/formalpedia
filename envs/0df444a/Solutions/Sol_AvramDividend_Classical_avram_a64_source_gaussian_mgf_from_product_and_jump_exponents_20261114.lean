-- Prove2me | solution 1 for AvramDividend.Classical.avram_a64_source_gaussian_mgf_from_product_and_jump_exponents_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:34:47.90023+00:00
-- url     : https://prove2.me/submissions/1295ce3c-b818-43fb-b791-dd655dbf9e73

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

/-- Remove the known compound jump factor from an exact source exponential moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (G J : Ω → ℝ) (θ a b c : ℝ)
    (hFactor :
      (∫ ω, Real.exp (θ * (G ω + J ω)) ∂P) =
        (∫ ω, Real.exp (θ * G ω) ∂P) *
          (∫ ω, Real.exp (θ * J ω) ∂P))
    (hSource :
      (∫ ω, Real.exp (θ * (G ω + J ω)) ∂P) = Real.exp a)
    (hJump : (∫ ω, Real.exp (θ * J ω) ∂P) = Real.exp b)
    (hBalance : a - b = c) :
    (∫ ω, Real.exp (θ * G ω) ∂P) = Real.exp c := by
  have hMul :
      (∫ ω, Real.exp (θ * G ω) ∂P) * Real.exp b =
        Real.exp a := by
    calc
      (∫ ω, Real.exp (θ * G ω) ∂P) * Real.exp b =
          (∫ ω, Real.exp (θ * G ω) ∂P) *
            (∫ ω, Real.exp (θ * J ω) ∂P) := by rw [hJump]
      _ = (∫ ω, Real.exp (θ * (G ω + J ω)) ∂P) := hFactor.symm
      _ = Real.exp a := hSource
  calc
    (∫ ω, Real.exp (θ * G ω) ∂P) =
        Real.exp a / Real.exp b :=
      (eq_div_iff (Real.exp_ne_zero b)).2 hMul
    _ = Real.exp (a - b) := by rw [Real.exp_sub]
    _ = Real.exp c := by rw [hBalance]
