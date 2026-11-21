-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_future_negative_mark_indep_centered_integral_crosszero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:32:50.221955+00:00
-- url     : https://prove2.me/submissions/c22ce01a-918f-43fe-8702-b6a21c66026a

import Mathlib.Probability.Independence.Integration
open MeasureTheory ProbabilityTheory
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Past Future : Ω → ℝ)
    (hIndep : IndepFun Past Future P)
    (hPast : Integrable Past P)
    (hFuture : Integrable Future P)
    (hCentered : (∫ ω, Future ω ∂P) = 0) :
    (∫ ω, Past ω * Future ω ∂P) = 0 := by
  calc
    (∫ ω, Past ω * Future ω ∂P) =
        (∫ ω, Past ω ∂P) * (∫ ω, Future ω ∂P) :=
      ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral
        hIndep hPast.aestronglyMeasurable hFuture.aestronglyMeasurable
    _ = 0 := by rw [hCentered]; simp
