-- Prove2me | solution 1 for BanditAlgorithm.integral_exp_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T20:48:55.269768+00:00
-- url     : https://prove2.me/submissions/75779837-ecc6-48a5-b35e-3fec2b737551

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral


/-!
# The Gaussian integral with a linear term

`∫ exp(−a x² + c x) dx = √(π/a) · exp(c²/(4a))` for `a > 0`.

Mathlib has the pure Gaussian integral `∫ exp(−b x²) = √(π/b)` but not the
completed-square version with a linear term, which is what every "method of
mixtures" computation needs: mixing the bandit exponential martingale
`exp(λ z − λ² t/2)` over a Gaussian prior on the tilt `λ` is exactly this integral
with `a = (1+t)/2` and `c = z`, and produces the self-normalised weight
`(1+t)^{−1/2} exp(z²/(2(1+t)))`.

The proof is completing the square and translating.
-/

open MeasureTheory Real

namespace BanditAlgorithm

/-- **The Gaussian integral with a linear term.** -/
theorem integral_exp_quad_aux {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∫ x : ℝ, Real.exp (-a * x ^ 2 + c * x)
      = Real.sqrt (π / a) * Real.exp (c ^ 2 / (4 * a)) := by
  have hrw : (fun x : ℝ ↦ Real.exp (-a * x ^ 2 + c * x))
      = fun x : ℝ ↦ Real.exp (c ^ 2 / (4 * a)) *
        (fun y : ℝ ↦ Real.exp (-a * y ^ 2)) (x - c / (2 * a)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hrw, integral_const_mul,
    integral_sub_right_eq_self (fun y : ℝ ↦ Real.exp (-a * y ^ 2)) (c / (2 * a)),
    integral_gaussian]
  ring

/-- The mixture weight: integrating the exponential tilt `exp(λ z − λ² t / 2)`
against the standard Gaussian density in `λ`. -/
theorem integral_exp_tilt_mixture {t : ℝ} (ht : 0 ≤ t) (z : ℝ) :
    ∫ lam : ℝ, (Real.sqrt (2 * π))⁻¹ * Real.exp (-(lam ^ 2) / 2)
        * Real.exp (lam * z - lam ^ 2 * t / 2)
      = (Real.sqrt (1 + t))⁻¹ * Real.exp (z ^ 2 / (2 * (1 + t))) := by
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have ha : (0 : ℝ) < (1 + t) / 2 := by linarith
  have hrw : (fun lam : ℝ ↦ (Real.sqrt (2 * π))⁻¹ * Real.exp (-(lam ^ 2) / 2)
        * Real.exp (lam * z - lam ^ 2 * t / 2))
      = fun lam : ℝ ↦ (Real.sqrt (2 * π))⁻¹ *
        Real.exp (-((1 + t) / 2) * lam ^ 2 + z * lam) := by
    funext lam
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hrw, integral_const_mul, integral_exp_quad_aux ha z]
  have hsqrt : Real.sqrt (π / ((1 + t) / 2)) = Real.sqrt (2 * π) * (Real.sqrt (1 + t))⁻¹ := by
    rw [show π / ((1 + t) / 2) = (2 * π) / (1 + t) by field_simp]
    rw [Real.sqrt_div' _ (by positivity), div_eq_mul_inv]
  rw [hsqrt]
  have hexp : z ^ 2 / (4 * ((1 + t) / 2)) = z ^ 2 / (2 * (1 + t)) := by
    congr 1
    ring
  rw [hexp]
  have h2π : Real.sqrt (2 * π) ≠ 0 := by positivity
  field_simp

end BanditAlgorithm


theorem _root_.solution {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∫ x : ℝ, Real.exp (-a * x ^ 2 + c * x)
      = Real.sqrt (Real.pi / a) * Real.exp (c ^ 2 / (4 * a)) :=
  BanditAlgorithm.integral_exp_quad_aux ha c
