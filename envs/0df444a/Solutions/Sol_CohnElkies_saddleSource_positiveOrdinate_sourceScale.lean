-- Prove2me | solution 1 for CohnElkies.saddleSource_positiveOrdinate_sourceScale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/15e5bede-38d7-46c9-bae0-e5e27fa1fc57

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 1 ≤ u) :
    Real.log ℓ / 4 ≤ ℓ * (1 + u) := by
  have hlog := Real.log_le_sub_one_of_pos hℓ
  have hproduct :=
    mul_nonneg hℓ.le (sub_nonneg.mpr hu)
  nlinarith
end CohnElkies
