-- Prove2me | solution 1 for CohnElkies.eventualUpperBound_of_constructivePrimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/8ad4db04-fcf2-4128-8cb0-a2b5e5934013

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedProgram_le_normalizedCost

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (hupper : ConstructivePrimalUpperBound) : EventualUpperBound := by
  intro c hc
  filter_upwards [hupper c hc] with d ⟨f, hf⟩
  exact (normalizedProgram_le_normalizedCost f).trans hf
end CohnElkies
