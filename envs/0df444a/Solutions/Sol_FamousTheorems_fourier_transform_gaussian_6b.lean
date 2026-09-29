-- Prove2me | solution 1 for FamousTheorems.fourier_transform_gaussian_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:42:11.140827+00:00
-- url     : https://prove2.me/submissions/1a2f226a-7bf0-43dc-8b7a-74deecae6f47

import Mathlib

theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {b : ℂ} (hb : 0 < b.re) (w : V) :
    FourierTransform.fourier (fun v : V => Complex.exp (-b * (‖v‖ : ℂ) ^ 2)) w =
      ((Real.pi : ℂ) / b) ^ ((Module.finrank ℝ V : ℂ) / 2) * Complex.exp (-(Real.pi : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / b) :=
  fourier_gaussian_innerProductSpace hb w
