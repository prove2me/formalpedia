-- Prove2me | solution 1 for CohnElkies.saddleSourceGaussianMinusIntegrand_tail_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/eb7ef328-7874-4730-9090-8987298e2557

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (ε ℓ u R : ℝ) :
    (∫ T : ℝ in saddleGaussianTailSet R,
      ‖saddleSourceGaussianMinusIntegrand ε ℓ u T‖) =
      ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
        (∫ T : ℝ in saddleGaussianTailSet R,
          saddleSourceGaussianKernel ε ℓ u T) := by
  calc
    (∫ T : ℝ in saddleGaussianTailSet R,
      ‖saddleSourceGaussianMinusIntegrand ε ℓ u T‖) =
      ∫ T : ℝ in saddleGaussianTailSet R,
        saddleSourceGaussianKernel ε ℓ u T *
          ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with T
      unfold saddleSourceGaussianMinusIntegrand
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (show 0 < saddleSourceGaussianKernel ε ℓ u T by
          unfold saddleSourceGaussianKernel
          positivity)]
    _ = ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
        (∫ T : ℝ in saddleGaussianTailSet R,
          saddleSourceGaussianKernel ε ℓ u T) := by
      rw [integral_mul_const]
      ring
end CohnElkies
