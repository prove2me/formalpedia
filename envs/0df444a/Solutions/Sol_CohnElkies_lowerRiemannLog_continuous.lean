-- Prove2me | solution 1 for CohnElkies.lowerRiemannLog_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/fc257da7-6f0c-4001-b5d7-5ad48fc18f17

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
theorem _root_.solution
    {T : ℝ} (hT : T ≠ 0) :
    Continuous (lowerRiemannLog T) := by
  have hrad (x : ℝ) : 0 < x ^ 2 + T ^ 2 / 4 := by
    nlinarith [sq_nonneg x, sq_pos_of_ne_zero hT]
  have hsqrt :
      Continuous (fun x : ℝ =>
        Real.sqrt (x ^ 2 + T ^ 2 / 4)) := by
    fun_prop
  unfold lowerRiemannLog
  exact hsqrt.log (fun x =>
    (Real.sqrt_pos.mpr (hrad x)).ne')
end CohnElkies
