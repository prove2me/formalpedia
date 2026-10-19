-- Prove2me | solution 2 for CohnElkies.lowerRiemannLog_monotoneOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:09:08.728772+00:00
-- url     : https://prove2.me/submissions/65ebfd31-8ab1-4e50-87bb-40f678516428

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


theorem solution {T : ℝ} (hT : T ≠ 0) :
    MonotoneOn (lowerRiemannLog T) (Ici (0 : ℝ)) := by
  have hT2 : 0 < T ^ 2 := lt_of_le_of_ne (sq_nonneg T) (Ne.symm (pow_ne_zero 2 hT))
  intro a ha b hb hab
  have ha' : (0:ℝ) ≤ a := ha
  unfold lowerRiemannLog
  apply Real.log_le_log (Real.sqrt_pos.2 (by positivity))
  apply Real.sqrt_le_sqrt
  nlinarith

