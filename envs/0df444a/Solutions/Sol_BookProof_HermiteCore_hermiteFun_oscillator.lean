-- Prove2me | solution 1 for BookProof.HermiteCore.hermiteFun_oscillator
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:00:42.89012+00:00
-- url     : https://prove2.me/submissions/ca5e45e9-a146-443b-8a39-9a2d7ff36f54

-- Generated from ChapterHermiteFunctions.lean — solution of BookProof.HermiteCore.hermiteFun_oscillator
import Mathlib
import Definitions.Def_ChapterHermiteFunctions
import Theorems.Thm_BookProof_HermiteCore_hermiteR_ode
import Theorems.Thm_BookProof_HermiteCore_deriv_poly_mul_gaussH
open BookProof.HermiteCore









open MeasureTheory Polynomial Filter Topology FourierTransform SchwartzMap

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (x : ℝ) :
    -(deriv (deriv (hermiteFun n)) x) + x ^ 2 / 4 * hermiteFun n x
      = ((n : ℝ) + 1 / 2) * hermiteFun n x := by

  set q : Polynomial ℝ := derivative (hermiteR n) - C (1 / 2 : ℝ) * (X * hermiteR n) with hq
  have h1 : hermiteFun n = fun y : ℝ => (hermiteR n).eval y * gaussH y := rfl
  have h2 : deriv (hermiteFun n) = fun y : ℝ => q.eval y * gaussH y := by
    rw [h1, deriv_poly_mul_gaussH]
  have h3 : deriv (deriv (hermiteFun n)) x
      = (derivative q - C (1 / 2 : ℝ) * (X * q)).eval x * gaussH x := by
    rw [h2, deriv_poly_mul_gaussH]
  have hq' : derivative q = derivative (derivative (hermiteR n))
      - C (1 / 2 : ℝ) * (hermiteR n + X * derivative (hermiteR n)) := by
    rw [hq, derivative_sub, derivative_C_mul, derivative_mul, derivative_X, one_mul]
  have hode := congrArg (Polynomial.eval x) (hermiteR_ode n)
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_zero] at hode
  rw [h3, hq', hq, h1]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  linear_combination (-gaussH x) * hode
