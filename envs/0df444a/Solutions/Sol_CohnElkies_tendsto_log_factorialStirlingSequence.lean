-- Prove2me | solution 1 for CohnElkies.tendsto_log_factorialStirlingSequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/0df0b739-d56b-497f-bd68-4a7ca9d33483

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_factorialStirlingSequence

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology
namespace CohnElkies
theorem _root_.solution :
    Tendsto (fun k : ℕ => Real.log (Stirling.stirlingSeq k))
      atTop (nhds (Real.log (Real.sqrt Real.pi))) := by
  exact (Real.continuousAt_log (by positivity)).tendsto.comp
    tendsto_factorialStirlingSequence
end CohnElkies
