-- Prove2me | solution 2 for CohnElkies.saddleNegativeContour_piExponential_norm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:25:12.895784+00:00
-- url     : https://prove2.me/submissions/e578bc46-388b-4516-b970-02ee0d43acf7

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
    (ℓ : ℝ) (N : ℕ) (s : ℝ) :
    ‖Complex.exp
      ((((ℓ : ℂ) -
        ((saddleTaylorContour N : ℂ) +
          (s : ℂ) * Complex.I)) *
          (Real.log Real.pi : ℂ) / 2))‖ =
      Real.exp
        ((ℓ - saddleTaylorContour N) *
          Real.log Real.pi / 2) := by
  have h : (((ℓ : ℂ) - ((saddleTaylorContour N : ℂ) + (s : ℂ) * Complex.I)) * (Real.log Real.pi : ℂ) / 2)
      = (((ℓ - saddleTaylorContour N) * Real.log Real.pi / 2 : ℝ) : ℂ) +
        ((-(s * Real.log Real.pi / 2) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp]
  simp

