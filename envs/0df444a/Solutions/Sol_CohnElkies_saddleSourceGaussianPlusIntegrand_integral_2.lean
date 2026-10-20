-- Prove2me | solution 2 for CohnElkies.saddleSourceGaussianPlusIntegrand_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:35:57.747987+00:00
-- url     : https://prove2.me/submissions/4a3fe934-f41c-4d15-8e5c-76b854b151ad

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
    (∫ T : ℝ, saddleSourceGaussianPlusIntegrand ε ℓ u T) =
      (Real.sqrt
        (Real.pi /
          (ℓ * saddleSourceGaussianVariance ε ℓ u / 2)) : ℂ) *
        plusPolynomial ε (Complex.I * (u : ℂ)) := by
  unfold saddleSourceGaussianPlusIntegrand saddleSourceGaussianKernel
  rw [MeasureTheory.integral_mul_const, integral_complex_ofReal, integral_gaussian]

