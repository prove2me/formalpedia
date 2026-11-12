-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja21_independent_centered_real_components_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T15:01:27.539926+00:00
-- url     : https://prove2.me/submissions/9823d653-ee9b-4d97-9e77-62b89f959130

import Mathlib.Probability.Independence.Integration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G J : Ω → ℝ)
    (hIndep : ProbabilityTheory.IndepFun G J P)
    (hGMeas : AEStronglyMeasurable G P)
    (hJMeas : AEStronglyMeasurable J P)
    (hGzero : (∫ ω, G ω ∂P) = 0)
    (hJzero : (∫ ω, J ω ∂P) = 0) :
    (∫ ω, G ω * J ω ∂P) = 0 := by
  calc
    (∫ ω, G ω * J ω ∂P) =
        (∫ ω, G ω ∂P) * (∫ ω, J ω ∂P) :=
      ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral
        hIndep hGMeas hJMeas
    _ = 0 := by rw [hGzero, hJzero]; ring
