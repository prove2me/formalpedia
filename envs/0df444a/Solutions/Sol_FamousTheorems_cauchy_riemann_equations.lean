-- Prove2me | solution 1 for FamousTheorems.cauchy_riemann_equations
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:34:18.836998+00:00
-- url     : https://prove2.me/submissions/6f1e615c-60c4-4338-8e5e-02a427e43c41

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {x : ℂ} :
    DifferentiableAt ℂ f x ↔
      DifferentiableAt ℝ f x ∧ fderiv ℝ f x Complex.I = Complex.I • fderiv ℝ f x 1 :=
  differentiableAt_complex_iff_differentiableAt_real
