-- Prove2me | solution 2 for CohnElkies.saddleNegativeRelativeCoefficient_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:10:01.952448+00:00
-- url     : https://prove2.me/submissions/b2236bb2-6764-4860-a604-5f267e34bc99

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


theorem solution
    {ε : ℝ} (hε : 0 < ε) :
    0 ≤ saddleNegativeRelativeCoefficient ε := by
  have hm : 0 ≤ saddleNegativeFrequencyMass ε := by
    unfold saddleNegativeFrequencyMass
    exact integral_nonneg fun s => by unfold saddleNegativeFrequencyMajorant; positivity
  unfold saddleNegativeRelativeCoefficient beta
  positivity

