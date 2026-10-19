-- Prove2me | solution 1 for CohnElkies.saddleSourceGaussianMinusIntegrand_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/fa375a62-4630-4dde-acb8-be63403da066

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceGaussianKernel_integral

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    (ε ℓ u : ℝ) :
    (∫ T : ℝ, saddleSourceGaussianMinusIntegrand ε ℓ u T) =
      (Real.sqrt
        (Real.pi /
          (ℓ * saddleSourceGaussianVariance ε ℓ u / 2)) : ℂ) *
        minusPolynomial ε (Complex.I * (u : ℂ)) := by
  unfold saddleSourceGaussianMinusIntegrand
  rw [MeasureTheory.integral_mul_const, integral_complex_ofReal,
    saddleSourceGaussianKernel_integral]
end CohnElkies
