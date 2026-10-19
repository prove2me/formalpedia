-- Prove2me | solution 1 for CohnElkies.saddleNegativeFrequencyMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/f9d12f4e-f484-4ed3-96af-1cce801d9d76

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution (ε : ℝ) :
    0 ≤ saddleNegativeFrequencyMass ε := by
  unfold saddleNegativeFrequencyMass
  apply integral_nonneg
  intro s
  unfold saddleNegativeFrequencyMajorant
  positivity
end CohnElkies
