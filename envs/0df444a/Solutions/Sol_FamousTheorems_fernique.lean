-- Prove2me | solution 1 for FamousTheorems.fernique
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:17:10.316303+00:00
-- url     : https://prove2.me/submissions/059da117-c5c9-44f0-a22b-17675557bb0e

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E] (μ : MeasureTheory.Measure E) [ProbabilityTheory.IsGaussian μ] :
    ∃ C : ℝ, 0 < C ∧ MeasureTheory.Integrable (fun x => Real.exp (C * ‖x‖ ^ 2)) μ :=
  ProbabilityTheory.IsGaussian.exists_integrable_exp_sq μ
