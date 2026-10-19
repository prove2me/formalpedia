-- Prove2me | solution 2 for CohnElkies.saddleSourceContour_piExponential_norm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:10:41.615096+00:00
-- url     : https://prove2.me/submissions/f41ca877-dbd9-40b4-a7bb-99d2115b3b8d

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
    (ℓ u T : ℝ) :
    ‖Complex.exp
        (((ℓ : ℂ) - saddleSourceMellinContour ℓ u T) *
          (Real.log Real.pi : ℂ) / 2)‖ =
      Real.exp (-(ℓ * u) * Real.log Real.pi / 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [saddleSourceMellinContour]
  ring

