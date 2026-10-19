-- Prove2me | solution 2 for CohnElkies.tendsto_log_two_mul_nat_div_nat
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:05:32.336518+00:00
-- url     : https://prove2.me/submissions/c894e28d-b165-4d20-a5cf-0845470deb0a

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
    Tendsto (fun k : ℕ =>
      Real.log ((2 : ℝ) * (k : ℝ)) / (k : ℝ))
      atTop (nhds 0) := by
  have h1 : Tendsto (fun k : ℕ => Real.log (k:ℝ) / (k:ℝ)) atTop (nhds 0) :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop |>.congr (fun k => by simp)
  have h2 : Tendsto (fun k : ℕ => Real.log 2 / (k:ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine (by simpa using h2.add h1 : Tendsto (fun k : ℕ => Real.log 2 / (k:ℝ) + Real.log (k:ℝ) / (k:ℝ)) atTop (nhds 0)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  rw [Real.log_mul (by norm_num) (by positivity), add_div]

