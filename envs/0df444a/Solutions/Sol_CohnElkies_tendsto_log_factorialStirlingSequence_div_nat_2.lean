-- Prove2me | solution 2 for CohnElkies.tendsto_log_factorialStirlingSequence_div_nat
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:12:04.811826+00:00
-- url     : https://prove2.me/submissions/b4c32023-8703-457c-9083-05be87544d43

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
      (fun k : ℕ => Real.log (Stirling.stirlingSeq k) / (k : ℝ))
      atTop (nhds 0) := by
  have h := Stirling.tendsto_stirlingSeq_sqrt_pi
  have hl := (Real.continuousAt_log (Real.sqrt_pos.2 Real.pi_pos).ne').tendsto.comp h
  exact hl.div_atTop tendsto_natCast_atTop_atTop

