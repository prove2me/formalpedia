-- Prove2me | solution 2 for CohnElkies.saddleSourceGaussianMinusIntegrand_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:13:37.143412+00:00
-- url     : https://prove2.me/submissions/ef00fed7-c4bc-4b8e-a9ff-1312c2067e19

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology


theorem solution
    (ε ℓ u : ℝ) :
    (∫ T : ℝ, saddleSourceGaussianMinusIntegrand ε ℓ u T) =
      (Real.sqrt
        (Real.pi /
          (ℓ * saddleSourceGaussianVariance ε ℓ u / 2)) : ℂ) *
        minusPolynomial ε (Complex.I * (u : ℂ)) := by
  unfold saddleSourceGaussianMinusIntegrand saddleSourceGaussianKernel
  rw [MeasureTheory.integral_mul_const, integral_complex_ofReal, integral_gaussian]

