-- Prove2me | solution 1 for CohnElkies.strip_abs_log_le_add_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/df4153f8-53c7-47ea-be91-de061e41b5aa

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
theorem _root_.solution {x : ℝ} (hx : 0 < x) :
    |Real.log x| ≤ x + 2 * x ^ (-(1 / 2 : ℝ)) := by
  by_cases hlarge : 1 ≤ x
  · rw [abs_of_nonneg (Real.log_nonneg hlarge)]
    have hlog := Real.log_le_sub_one_of_pos hx
    have hpower := Real.rpow_pos_of_pos hx (-(1 / 2 : ℝ))
    nlinarith
  · have hsmall : x ≤ 1 := le_of_not_ge hlarge
    rw [abs_of_nonpos (Real.log_nonpos hx.le hsmall)]
    have hpower := Real.rpow_pos_of_pos hx (-(1 / 2 : ℝ))
    have hlog := Real.log_le_sub_one_of_pos hpower
    rw [Real.log_rpow hx] at hlog
    nlinarith
end CohnElkies
