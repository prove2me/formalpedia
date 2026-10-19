-- Prove2me | solution 1 for CohnElkies.saddleSourceContour_inversePower_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/b9888f43-c873-4e3e-a93f-5cd4e45ba4ff

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
    (ℓ u v T : ℝ) :
    saddleMellinInversePower (Real.exp v)
        (saddleSourceMellinContour ℓ u T) =
      ((Real.exp (-(ℓ * (1 + u) * v)) : ℝ) : ℂ) *
        Complex.exp
          (Complex.I * ((ℓ * T * v : ℝ) : ℂ)) := by
  unfold saddleMellinInversePower
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos v).ne'),
    ← Complex.ofReal_log (Real.exp_pos v).le,
    Real.log_exp,
    Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  unfold saddleSourceMellinContour
  push_cast
  ring
end CohnElkies
