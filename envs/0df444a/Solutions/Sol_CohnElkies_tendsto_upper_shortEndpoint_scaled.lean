-- Prove2me | solution 1 for CohnElkies.tendsto_upper_shortEndpoint_scaled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/1e9eaac9-bc57-49bc-82ed-8d9676a70494

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
namespace CohnElkies
theorem _root_.solution :
    Tendsto (fun ε : ℝ => ε * shortEndpoint ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hlog := tendsto_log_mul_rpow_nhdsGT_zero
    (by norm_num : (0 : ℝ) < 1)
  simp only [Real.rpow_one] at hlog
  have hscaled := hlog.const_mul (-10 : ℝ)
  convert! hscaled using 1
  · ext ε
    unfold shortEndpoint
    rw [one_div, Real.log_inv]
    ring
  · norm_num
end CohnElkies
