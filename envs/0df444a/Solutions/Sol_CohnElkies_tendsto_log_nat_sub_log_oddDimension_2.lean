-- Prove2me | solution 2 for CohnElkies.tendsto_log_nat_sub_log_oddDimension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:34:03.627606+00:00
-- url     : https://prove2.me/submissions/15a79b64-35d3-4196-ba80-49da3968c20e

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology


theorem solution :
    Tendsto
      (fun k : ℕ =>
        Real.log (k : ℝ) - Real.log (2 * (k : ℝ) + 1))
      atTop (nhds (Real.log (1 / 2 : ℝ))) := by
  have h1 : Tendsto (fun k : ℕ => (k : ℝ) / (2 * (k : ℝ) + 1)) atTop (nhds (1 / 2 : ℝ)) := by
    have h := tendsto_natCast_div_add_atTop (𝕜 := ℝ) (1 / 2 : ℝ)
    have := h.const_mul (1 / 2 : ℝ)
    simp only [mul_one] at this
    refine this.congr fun k => ?_
    field_simp <;> ring
  have h2 := ((Real.continuousAt_log (by norm_num : (1 / 2 : ℝ) ≠ 0)).tendsto).comp h1
  refine h2.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with k hk
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  simp only [Function.comp_apply]
  rw [Real.log_div hk'.ne' (by positivity)]

