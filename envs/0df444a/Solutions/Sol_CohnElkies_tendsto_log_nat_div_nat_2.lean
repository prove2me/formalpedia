-- Prove2me | solution 2 for CohnElkies.tendsto_log_nat_div_nat
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:07:27.880829+00:00
-- url     : https://prove2.me/submissions/c2bcde12-6d82-455a-8c58-1c24864cbc7d

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
    Tendsto (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ))
      atTop (nhds 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  simpa [Function.comp_def] using h

