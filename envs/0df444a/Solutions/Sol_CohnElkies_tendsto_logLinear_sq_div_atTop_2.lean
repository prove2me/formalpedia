-- Prove2me | solution 2 for CohnElkies.tendsto_logLinear_sq_div_atTop
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:00:31.310539+00:00
-- url     : https://prove2.me/submissions/c6e5e483-2fb4-45b8-8d5e-cdf35b1fcb9c

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
    Tendsto
      (fun ℓ : ℝ => (20 * Real.log ℓ + 1) ^ 2 / ℓ)
      atTop (𝓝 0) := by
  have h2 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h0 : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero
  have := ((h2.const_mul 400).add (h1.const_mul 40)).add h0
  simp only [mul_zero, add_zero, one_mul, pow_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  field_simp
  ring

