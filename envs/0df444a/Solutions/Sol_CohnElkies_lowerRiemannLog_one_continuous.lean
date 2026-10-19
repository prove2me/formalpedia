-- Prove2me | solution 1 for CohnElkies.lowerRiemannLog_one_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/9f6e8ba4-5291-4c60-bd1c-d985930cf611

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution :
    Continuous (fun T : ℝ => lowerRiemannLog T 1) := by
  have hrad (T : ℝ) : 0 < (1 : ℝ) + T ^ 2 / 4 := by
    nlinarith [sq_nonneg T]
  have hsqrt :
      Continuous (fun T : ℝ =>
        Real.sqrt ((1 : ℝ) + T ^ 2 / 4)) := by
    fun_prop
  have h := hsqrt.log
    (fun T => (Real.sqrt_pos.mpr (hrad T)).ne')
  simpa [lowerRiemannLog] using! h
end CohnElkies
