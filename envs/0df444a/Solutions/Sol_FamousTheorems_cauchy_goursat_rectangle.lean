-- Prove2me | solution 1 for FamousTheorems.cauchy_goursat_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T21:42:36.311984+00:00
-- url     : https://prove2.me/submissions/1033bdc9-3995-4ac6-83e6-1aa0cd107a61

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E) (z w : ℂ)
    (H : DifferentiableOn ℂ f (Complex.reProdIm (Set.uIcc z.re w.re) (Set.uIcc z.im w.im))) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * Complex.I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * Complex.I)) +
      Complex.I • (∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I)) -
      Complex.I • (∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I)) = 0 := by
  exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w H
