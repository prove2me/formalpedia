-- Prove2me | solution 1 for FamousTheorems.newton_binomial_series_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:46:01.72819+00:00
-- url     : https://prove2.me/submissions/6959712c-8be6-4aa4-ae05-aa46698b2150

import Mathlib

theorem solution (a : ℂ) : HasFPowerSeriesOnBall (fun x : ℂ => (1 + x) ^ a) (binomialSeries ℂ a) 0 1 :=
  Complex.one_add_cpow_hasFPowerSeriesOnBall_zero
