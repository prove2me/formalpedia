-- Prove2me | solution 1 for FamousTheorems.harmonic_mean_value_property_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:42:08.103505+00:00
-- url     : https://prove2.me/submissions/925b92a3-2257-4eae-8b8f-9c58024ba826

import Mathlib

theorem solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : ℂ → F} {c : ℂ} {R : ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd f (Metric.closedBall c |R|)) : Real.circleAverage f c R = f c :=
  hf.circleAverage_eq
