-- Prove2me | solution 1 for CohnElkies.eventualLowerBound_of_uniform_and_constructive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/1251d414-8e4d-4740-9227-bad5f31533a6

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
namespace CohnElkies
theorem _root_.solution
    (hlower : UniformAdmissibleLowerBound)
    (hupper : ConstructivePrimalUpperBound) : EventualLowerBound := by
  intro c hc
  have haux : criticalRadius < criticalRadius + 1 := by linarith
  filter_upwards [hlower c hc, hupper (criticalRadius + 1) haux]
    with d hcost ⟨f, _⟩
  unfold normalizedProgram
  refine le_csInf ⟨normalizedCost f, f, rfl⟩ ?_
  rintro _ ⟨g, rfl⟩
  exact hcost g
end CohnElkies
