-- Prove2me | solution 1 for AvramDividend.Classical.normalized_derivative_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-03T12:18:55.583084+00:00
-- url     : https://prove2.me/submissions/64e40c4b-7f71-492f-bfb2-08e2d5a9d126

import Mathlib

open Set

/-
Normalized monotonicity of the tilted scale function forces a lower bound on
the derivative of the scale function itself.

Suppose `g x = exp (-phi * x) * W x` is monotone on `(0, inf)` and `W` is
differentiable at a point `x > 0`. Then `phi * W x <= deriv W x`.

Proof. Since `g` is monotone on the open set `Ioi 0`, its derivative within
that set at `x` is nonnegative (`MonotoneOn.derivWithin_nonneg`), and because
`Ioi 0` is open at `x` the `derivWithin` equals the plain `deriv`
(`derivWithin_of_isOpen`). Expanding `g' x` by the product rule gives

    g' x = exp (-phi * x) * (-phi * W x + W' x).

Nonnegativity, together with `exp (-phi * x) > 0`, forces
`-phi * W x + W' x >= 0`, which is the claim.

This is the whole analytic content of the proposed bridge
`scaleFunction_tilted_positive_monotone`: positivity of the exponential
factor is what lets the derivative's sign be read off the bracket. The
stochastic premise (that such a `phi` exists) is NOT proved here.
-/
theorem solution
    (W : ℝ → ℝ) (φ x : ℝ)
    (hg : MonotoneOn (fun t : ℝ => Real.exp (-φ * t) * W t) (Ioi 0))
    (hx : 0 < x) (hW : DifferentiableAt ℝ W x) :
    φ * W x ≤ deriv W x := by
  have hgrad :
      0 ≤ deriv (fun t : ℝ => Real.exp (-φ * t) * W t) x := by
    rw [← derivWithin_of_isOpen isOpen_Ioi (show x ∈ Ioi (0 : ℝ) from hx)]
    exact hg.derivWithin_nonneg
  have hlinear : HasDerivAt (fun t : ℝ => -φ * t) (-φ) x := by
    simpa using (hasDerivAt_id x).const_mul (-φ)
  have hprod :
      HasDerivAt (fun t : ℝ => Real.exp (-φ * t) * W t)
        ((Real.exp (-φ * x) * (-φ)) * W x +
          Real.exp (-φ * x) * deriv W x) x :=
    hlinear.exp.mul hW.hasDerivAt
  rw [hprod.deriv] at hgrad
  have hpos : 0 < Real.exp (-φ * x) := Real.exp_pos _
  by_contra hnot
  have hlt : deriv W x < φ * W x := lt_of_not_ge hnot
  have : 0 < Real.exp (-φ * x) * (φ * W x - deriv W x) :=
    mul_pos hpos (sub_pos.mpr hlt)
  nlinarith
