-- Prove2me | solution 1 for FamousTheorems.poisson_integral_formula
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:29:22.342646+00:00
-- url     : https://prove2.me/submissions/5374923f-74bc-4758-a98e-142c2cef8b95

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {c w : ℂ} {R : ℝ}
    (hf : DiffContOnCl ℂ f (Metric.ball c R)) (hw : w ∈ Metric.ball c R) :
    Real.circleAverage (poissonKernel c w • f) c R = f w :=
  hf.circleAverage_poissonKernel_smul hw
