-- Prove2me | solution 1 for FamousTheorems.plancherel_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:13:53.993917+00:00
-- url     : https://prove2.me/submissions/b230ecee-f355-426c-9d89-77566829a55d

import Mathlib

theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f : SchwartzMap V H) : ∫ ξ, ‖FourierTransform.fourier f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 :=
  SchwartzMap.integral_norm_sq_fourier f
