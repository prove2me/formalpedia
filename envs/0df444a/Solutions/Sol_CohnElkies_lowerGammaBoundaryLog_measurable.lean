-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/eb7c17c3-f547-4f2c-9d54-c9d3352c015f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_continuousOn

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ : ℝ} (hℓ : 0 < ℓ) (R : ℝ) :
    Measurable (lowerGammaBoundaryLog ℓ R) := by
  apply measurable_of_continuousOn_compl_singleton (0 : ℝ)
  apply lowerGammaBoundaryLog_continuousOn hℓ R
  intro y hy
  simpa using! hy
end CohnElkies
