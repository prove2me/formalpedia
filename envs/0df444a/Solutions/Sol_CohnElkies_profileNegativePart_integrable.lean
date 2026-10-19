-- Prove2me | solution 1 for CohnElkies.profileNegativePart_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/50491454-adfa-45ba-8e22-a71086b73077

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
namespace CohnElkies
theorem _root_.solution {φ : ℝ → ℝ}
    (hφ : Integrable φ) : Integrable (profileNegativePart φ) := by
  change Integrable ((-φ) ⊔ (0 : ℝ → ℝ))
  exact hφ.neg.sup (integrable_zero ℝ ℝ volume)
end CohnElkies
