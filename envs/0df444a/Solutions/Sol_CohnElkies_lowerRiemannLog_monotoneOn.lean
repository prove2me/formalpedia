-- Prove2me | solution 1 for CohnElkies.lowerRiemannLog_monotoneOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/f4c6acf6-f128-4f65-9af0-2168da6b16df

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
theorem _root_.solution {T : ℝ} (hT : T ≠ 0) :
    MonotoneOn (lowerRiemannLog T) (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  have hrad : 0 < x ^ 2 + T ^ 2 / 4 := by
    nlinarith [sq_nonneg x, sq_pos_of_ne_zero hT]
  have hsquares : x ^ 2 ≤ y ^ 2 :=
    (sq_le_sq₀ hx hy).2 hxy
  unfold lowerRiemannLog
  exact Real.log_le_log (Real.sqrt_pos.2 hrad)
    (Real.sqrt_le_sqrt (by linarith))
end CohnElkies
