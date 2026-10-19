-- Prove2me | solution 2 for CohnElkies.eventualLowerBound_of_uniform_and_constructive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:13:51.83443+00:00
-- url     : https://prove2.me/submissions/072c8c09-5f29-4bbb-a049-2f6c5b12c97d

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
    (hlower : UniformAdmissibleLowerBound)
    (hupper : ConstructivePrimalUpperBound) : EventualLowerBound := by
  intro c hc
  have hcr : (0:ℝ) < criticalRadius := by unfold criticalRadius; exact inv_pos.2 Real.pi_pos
  filter_upwards [hlower c hc, hupper (criticalRadius + 1) (by linarith)] with d h1 h2
  obtain ⟨f, -⟩ := h2
  unfold normalizedProgram
  exact le_csInf ⟨normalizedCost f, f, rfl⟩ (by rintro y ⟨g, rfl⟩; exact h1 g)

