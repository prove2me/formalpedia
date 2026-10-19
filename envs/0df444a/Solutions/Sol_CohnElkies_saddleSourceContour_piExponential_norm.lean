-- Prove2me | solution 1 for CohnElkies.saddleSourceContour_piExponential_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/6ff9aed6-7058-4078-ac87-57e496888e9c

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
namespace CohnElkies
theorem _root_.solution
    (ℓ u T : ℝ) :
    ‖Complex.exp
        (((ℓ : ℂ) - saddleSourceMellinContour ℓ u T) *
          (Real.log Real.pi : ℂ) / 2)‖ =
      Real.exp (-(ℓ * u) * Real.log Real.pi / 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [saddleSourceMellinContour, Complex.mul_re]
  ring
end CohnElkies
