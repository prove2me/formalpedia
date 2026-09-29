-- Prove2me | solution 1 for FamousTheorems.gauss_mean_value_holomorphic
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:29:21.820209+00:00
-- url     : https://prove2.me/submissions/790a616f-cd62-4e73-8cc5-10e915bf5eab

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : DiffContOnCl ℂ f (Metric.ball c |R|)) :
    Real.circleAverage f c R = f c :=
  hf.circleAverage
