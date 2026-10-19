-- Prove2me | solution 2 for CohnElkies.profileNegativePart_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:10:55.075039+00:00
-- url     : https://prove2.me/submissions/73ed2a83-acc4-429b-bdfe-2fc4404fe4ee

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology


theorem solution {φ : ℝ → ℝ}
    (hφ : Integrable φ) : Integrable (profileNegativePart φ) := by
  unfold profileNegativePart
  exact hφ.neg.pos_part

