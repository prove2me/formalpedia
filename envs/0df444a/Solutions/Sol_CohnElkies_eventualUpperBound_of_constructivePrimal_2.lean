-- Prove2me | solution 2 for CohnElkies.eventualUpperBound_of_constructivePrimal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:51:43.529685+00:00
-- url     : https://prove2.me/submissions/4525ff3f-1c12-4b7d-bbe0-31fd2488368c

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology


theorem solution
    (hupper : ConstructivePrimalUpperBound) : EventualUpperBound := by
  intro c hc
  have hcpos : 0 < c := lt_trans (by unfold criticalRadius; exact inv_pos.mpr Real.pi_pos) hc
  filter_upwards [hupper c hc] with d hd
  obtain ⟨f, hf⟩ := hd
  unfold normalizedProgram
  by_cases hb : BddBelow (Set.range (normalizedCost (d := d)))
  · exact (csInf_le hb ⟨f, rfl⟩).trans hf
  · rw [Real.sInf_of_not_bddBelow hb]; exact hcpos.le

