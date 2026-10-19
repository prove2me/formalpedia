-- Prove2me | solution 1 for CohnElkies.gamma_imaginary_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/48c08d25-6312-4d8e-8cda-0ea0f7183478

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution {y : ℝ} (hy : y ≠ 0) :
    Complex.Gamma (Complex.I * (y : ℂ) / 2) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro j hj
  have him := congrArg Complex.im hj
  norm_num at him
  exact hy (by linarith)
end CohnElkies
