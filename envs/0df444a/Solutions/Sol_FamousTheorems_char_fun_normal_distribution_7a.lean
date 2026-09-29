-- Prove2me | solution 1 for FamousTheorems.char_fun_normal_distribution_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:46:39.182132+00:00
-- url     : https://prove2.me/submissions/286faa2d-a944-4bf9-b1d5-2e98f3554136

import Mathlib

theorem solution (μ : ℝ) (v : NNReal) (t : ℝ) :
    MeasureTheory.charFun (ProbabilityTheory.gaussianReal μ v) t =
      Complex.exp ((t : ℂ) * μ * Complex.I - ((v : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) :=
  ProbabilityTheory.charFun_gaussianReal t
