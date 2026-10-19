-- Prove2me | solution 1 for CohnElkies.complexWallisPhaseKernel_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/c47b1610-34dc-4348-b885-79aace64e161

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (a u t : ℝ) :
    (complexWallisPhaseKernel
      ((a : ℂ) - Complex.I * (u : ℂ)) t).re =
        lowerWallisRegularizedPhaseKernel a u t := by
  unfold complexWallisPhaseKernel lowerWallisRegularizedPhaseKernel
  rw [← Complex.ofReal_pow]
  rw [Complex.div_ofReal_re]
  simp [Complex.mul_re, Complex.exp_re, Complex.exp_im]
  ring
end CohnElkies
