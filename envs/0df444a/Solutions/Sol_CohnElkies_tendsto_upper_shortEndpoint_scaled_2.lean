-- Prove2me | solution 2 for CohnElkies.tendsto_upper_shortEndpoint_scaled
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:27:02.895385+00:00
-- url     : https://prove2.me/submissions/8101ccd4-63d3-4853-a4d4-773708bbc4e5

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution :
    Tendsto (fun ε : ℝ => ε * shortEndpoint ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have h := (tendsto_log_mul_rpow_nhdsGT_zero one_pos).const_mul (-10)
  simp only [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have he : (0:ℝ) < ε := hε
  unfold shortEndpoint
  rw [Real.rpow_one, one_div, Real.log_inv]
  ring

