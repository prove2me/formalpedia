-- Prove2me | solution 1 for AvramDividend.Classical.exp_tilt_deriv_pos_of_positive_factor
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:26:44.044615+00:00
-- url     : https://prove2.me/submissions/2f8012ed-2dd3-48c6-9449-f7fa3157c8ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical

theorem solution
    (φ : ℝ) (hφ : 0 < φ) (V : ℝ → ℝ)
    (hpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ V x)
    (hderiv : ∀ x : ℝ, 0 < x → 0 ≤ deriv V x) :
    ∀ x : ℝ, 0 < x →
      0 < deriv (fun t : ℝ => Real.exp (φ * t) * V t) x := by
  intro x hx
  have h := (((hasDerivAt_id x).const_mul φ).exp).mul (hdiff x hx).hasDerivAt
  have he : deriv (fun t : ℝ => Real.exp (φ * t) * V t) x =
      Real.exp (φ * x) * φ * V x + Real.exp (φ * x) * deriv V x := by
    simpa only [Pi.mul_def, id_eq, mul_one] using h.deriv
  rw [he]
  have hp := mul_pos (mul_pos (Real.exp_pos (φ * x)) hφ) (hpos x hx)
  have hn := mul_nonneg (Real.exp_pos (φ * x)).le (hderiv x hx)
  dsimp at *
  nlinarith

#print axioms solution
