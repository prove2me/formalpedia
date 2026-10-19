-- Prove2me | solution 1 for CohnElkies.saddleSourceCosineQuadraticRemainder_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/c49f2585-5407-4bfc-8fe6-a433936027a3

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceShiftedCosine_eq_imaginaryExponentials

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (a u T : ℝ) :
    saddleSourceCosineQuadraticRemainder a u T =
      ((Real.exp (-(u * a)) / 2 : ℝ) : ℂ) *
        (upperImaginaryExp (a * T) - 1 -
          Complex.I * ((a * T : ℝ) : ℂ) +
            (((a * T) ^ 2 / 2 : ℝ) : ℂ)) +
      ((Real.exp (u * a) / 2 : ℝ) : ℂ) *
        (upperImaginaryExp (-(a * T)) - 1 -
          Complex.I * ((-(a * T) : ℝ) : ℂ) +
            (((-(a * T)) ^ 2 / 2 : ℝ) : ℂ)) := by
  unfold saddleSourceCosineQuadraticRemainder
  rw [saddleSourceShiftedCosine_eq_imaginaryExponentials,
    Real.cosh_eq, Real.sinh_eq]
  push_cast
  ring
end CohnElkies
