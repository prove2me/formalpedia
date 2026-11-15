-- Prove2me | solution 1 for AvramDividend.Classical.avram_a51_independent_original_exponential_factors_integral_factorisation_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:57:45.427203+00:00
-- url     : https://prove2.me/submissions/e1c25bd3-fa49-4992-ba5e-d7900e5f9e59

import Mathlib.Probability.Independence.Integration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (G J : Ω → ℝ) (θ : ℝ)
    (hInd : IndepFun (fun ω => Real.exp (θ * G ω))
      (fun ω => Real.exp (θ * J ω)) P)
    (hG : Integrable (fun ω => Real.exp (θ * G ω)) P)
    (hJ : Integrable (fun ω => Real.exp (θ * J ω)) P) :
    (∫ ω, Real.exp (θ * (G ω + J ω)) ∂P) =
      (∫ ω, Real.exp (θ * G ω) ∂P) *
      (∫ ω, Real.exp (θ * J ω) ∂P) := by
  calc
    (∫ ω, Real.exp (θ * (G ω + J ω)) ∂P) =
        ∫ ω, Real.exp (θ * G ω) * Real.exp (θ * J ω) ∂P := by
          congr 1
          funext ω
          rw [mul_add, Real.exp_add]
    _ = (∫ ω, Real.exp (θ * G ω) ∂P) *
        (∫ ω, Real.exp (θ * J ω) ∂P) :=
          hInd.integral_mul_eq_mul_integral hG.aestronglyMeasurable hJ.aestronglyMeasurable
