-- Prove2me | solution 1 for Complex.negative_imaginary_exponential_eq_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/e3a17b5c-4966-40d8-9550-e5c55d7a7879

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
variable {d : ℕ} [Fact (0 < d)]
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
noncomputable section
open scoped BigOperators FourierTransform
omit [Fact (0 < d)]
namespace Complex
theorem _root_.solution (x m : EuclideanSpace ℝ (Fin d)) :
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (⟪x, m⟫_[ℝ] : ℂ))) =
    (starRingEnd ℂ) (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (⟪x, m⟫_[ℝ] : ℂ))) :=
  calc
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (⟪x, m⟫_[ℝ] : ℂ)))
        = Circle.exp (-2 * Real.pi * ⟪x, m⟫_[ℝ])
      := by
          rw [Circle.coe_exp]
          push_cast
          ring_nf
    _ = (starRingEnd ℂ) (Circle.exp (2 * Real.pi * ⟪x, m⟫_[ℝ]))
      := by rw [mul_assoc, neg_mul, ← mul_assoc, ← Circle.coe_inv_eq_conj, Circle.exp_neg]
    _ = (starRingEnd ℂ) (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (⟪x, m⟫_[ℝ] : ℂ)))
      := by
          rw [Circle.coe_exp]
          apply congrArg (starRingEnd ℂ)
          push_cast
          ring_nf
end Complex
