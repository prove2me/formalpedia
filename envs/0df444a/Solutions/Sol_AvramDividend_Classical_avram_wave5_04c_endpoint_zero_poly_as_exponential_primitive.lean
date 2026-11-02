-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_endpoint_zero_poly_as_exponential_primitive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:21:58.663257+00:00
-- url     : https://prove2.me/submissions/cc95f98a-79fe-4747-8cbc-e6028cd1b21d

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

/-! A polynomial of exp(-R) vanishing at R=0 is exactly the integrated
primitive of a polynomial with zero constant coefficient. -/
theorem solution (Q : Polynomial ℝ)
    (hQ : Polynomial.eval 1 Q = 0) :
    ∃ p : Polynomial ℝ, Polynomial.eval 0 p = 0 ∧
      ∀ R : ℝ,
        (∫ r in (0 : ℝ)..R,
          Polynomial.eval (Real.exp (-r)) p) =
            Polynomial.eval (Real.exp (-R)) Q := by
  let p : Polynomial ℝ := -Polynomial.X * Q.derivative
  have hp0 : Polynomial.eval 0 p = 0 := by simp [p]
  refine ⟨p, hp0, ?_⟩
  let g : ℝ → ℝ := fun r => Polynomial.eval (Real.exp (-r)) Q
  have hd (r : ℝ) :
      HasDerivAt g
        (Polynomial.eval (Real.exp (-r)) p) r := by
    have he : HasDerivAt (fun s : ℝ => Real.exp (-s))
        (-Real.exp (-r)) r := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_exp (-r)).comp r ((hasDerivAt_id r).neg)
    have hq : HasDerivAt (fun z : ℝ => Polynomial.eval z Q)
        (Polynomial.eval (Real.exp (-r)) Q.derivative) (Real.exp (-r)) :=
      Q.hasDerivAt _
    have hh := hq.comp r he
    simpa [g, p, Function.comp_def, mul_assoc, mul_comm, mul_left_comm] using hh
  have hdg : Differentiable ℝ g := fun r => (hd r).differentiableAt
  have hderiv (r : ℝ) :
      deriv g r = Polynomial.eval (Real.exp (-r)) p :=
    (hd r).deriv
  have hc : Continuous (deriv g) := by
    have hh : deriv g = fun r => Polynomial.eval (Real.exp (-r)) p :=
      funext hderiv
    rw [hh]
    fun_prop
  intro R
  have hi : IntervalIntegrable (deriv g) volume 0 R :=
    hc.intervalIntegrable _ _
  have hftc : (∫ r in (0 : ℝ)..R, deriv g r) = g R - g 0 :=
    intervalIntegral.integral_deriv_eq_sub
      (fun t ht => hdg t) hi
  have hInt :
      (∫ r in (0 : ℝ)..R,
        Polynomial.eval (Real.exp (-r)) p) = g R - g 0 := by
    simpa only [hderiv] using hftc
  simpa [g, hQ] using hInt
