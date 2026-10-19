-- Prove2me | solution 2 for CohnElkies.tendsto_log_factorialStirlingSequence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:14:30.492675+00:00
-- url     : https://prove2.me/submissions/d08ba2c0-692d-4ef3-a744-fb51c2ec303d

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
    Tendsto (fun k : ℕ => Real.log (Stirling.stirlingSeq k))
      atTop (nhds (Real.log (Real.sqrt Real.pi))) := by
  have hpos : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  exact ((Real.continuousAt_log hpos).tendsto).comp Stirling.tendsto_stirlingSeq_sqrt_pi

