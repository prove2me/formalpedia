-- Prove2me | solution 2 for CohnElkies.tendsto_upper_one_add_shortEndpoint_scaled
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:12:34.40826+00:00
-- url     : https://prove2.me/submissions/1753ca27-b5a0-4a79-927b-d915e576c1f1

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
    Tendsto (fun ε : ℝ => ε * (1 + shortEndpoint ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  unfold shortEndpoint
  have h := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos
  have h2 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have := h2.sub (h.const_mul 10)
  simp only [mul_zero, sub_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [Real.rpow_one, one_div, Real.log_inv]
  ring

