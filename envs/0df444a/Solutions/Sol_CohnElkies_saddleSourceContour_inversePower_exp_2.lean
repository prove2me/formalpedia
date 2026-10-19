-- Prove2me | solution 2 for CohnElkies.saddleSourceContour_inversePower_exp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:20.833+00:00
-- url     : https://prove2.me/submissions/1b0fd338-5476-4b16-bceb-582010206729

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
    (ℓ u v T : ℝ) :
    saddleMellinInversePower (Real.exp v)
        (saddleSourceMellinContour ℓ u T) =
      ((Real.exp (-(ℓ * (1 + u) * v)) : ℝ) : ℂ) *
        Complex.exp
          (Complex.I * ((ℓ * T * v : ℝ) : ℂ)) := by
  unfold saddleMellinInversePower saddleSourceMellinContour
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos v).ne'),
    ← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

