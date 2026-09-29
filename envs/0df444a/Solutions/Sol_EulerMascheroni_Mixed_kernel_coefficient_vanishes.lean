-- Prove2me | solution 1 for EulerMascheroni.Mixed.kernel_coefficient_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T12:48:19.542255+00:00
-- url     : https://prove2.me/submissions/613c9a65-c36a-44b0-9aaa-0ef032e8287d

import Definitions.Def_eulerMascheroni_mixedCover

theorem solution
    (P Q R S : Polynomial ℂ)
    (h : ∀ t : ℂ,
      P.eval (Complex.exp t) + Q.eval (Complex.exp t) * Complex.exp (Complex.exp t) +
      R.eval (Complex.exp t) * EulerMascheroni.Mixed.expEin (Complex.exp t) +
      S.eval (Complex.exp t) * EulerMascheroni.Mixed.kernelOnCover t = 0) :
    S.eval 1 = 0 := by
  let τ : ℂ := 2 * Real.pi * Complex.I
  have hτ : Complex.exp τ = 1 := Complex.exp_two_pi_mul_I
  have hshift : EulerMascheroni.Mixed.kernelOnCover τ =
      EulerMascheroni.Mixed.kernelOnCover 0 - Complex.exp 1 * τ := by
    simp only [EulerMascheroni.Mixed.kernelOnCover, hτ, Complex.exp_zero]
    ring
  have h0 := h 0
  have h1 := h τ
  simp only [Complex.exp_zero] at h0
  rw [hτ, hshift] at h1
  have hmul : S.eval 1 * (Complex.exp 1 * τ) = 0 := by
    linear_combination h0 - h1
  exact (mul_eq_zero.mp hmul).resolve_right
    (mul_ne_zero (Complex.exp_ne_zero 1) Complex.two_pi_I_ne_zero)

