-- Prove2me | solution 2 for CohnElkies.tendsto_factorialStirlingSequence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:55:53.614302+00:00
-- url     : https://prove2.me/submissions/ef327bf8-2648-44ab-8208-7dca2504f266

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
    Tendsto Stirling.stirlingSeq atTop
      (nhds (Real.sqrt Real.pi)) := by
  exact Stirling.tendsto_stirlingSeq_sqrt_pi

