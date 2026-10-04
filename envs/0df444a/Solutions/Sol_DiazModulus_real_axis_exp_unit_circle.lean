-- Prove2me | solution 1 for DiazModulus.real_axis_exp_unit_circle
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T05:39:08.567739+00:00
-- url     : https://prove2.me/submissions/b18a2d59-6847-40d6-9a05-756aa2801bfc

import Mathlib

theorem solution :
    ∀ γ : ℂ, γ.im = 0 →
      ‖Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))‖ = 1 := by
  intro γ hγ
  have hre : (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)).re = 0 := by
    simp [Complex.div_re, hγ]
  rw [Complex.norm_exp, hre, Real.exp_zero]
