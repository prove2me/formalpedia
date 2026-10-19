-- Prove2me | solution 2 for CohnElkies.tendsto_log_nat_div_oddDimension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:12:51.435971+00:00
-- url     : https://prove2.me/submissions/17b41886-140f-4a93-a272-cc8706ddabc8

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
      (fun k : ℕ => Real.log (k : ℝ) / (2 * (k : ℝ) + 1))
      atTop (nhds 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 2 1 1 two_ne_zero).comp tendsto_natCast_atTop_atTop
  simpa [Function.comp_def] using h

