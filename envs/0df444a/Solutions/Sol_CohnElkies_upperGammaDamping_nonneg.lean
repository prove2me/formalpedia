-- Prove2me | solution 1 for CohnElkies.upperGammaDamping_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/30419030-4d2e-4a52-bc2d-539169e8c712

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaMeasureDensity_pos

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (T : ℝ) :
    0 ≤ upperGammaDamping ℓ η T := by
  unfold upperGammaDamping
  apply setIntegral_nonneg measurableSet_Ioi
  intro a ha
  unfold upperGammaDampingIntegrand
  exact mul_nonneg
    (sub_nonneg.mpr (Real.cos_le_one _))
    (upperGammaMeasureDensity_pos
      (η := η) hℓ ha).le
end CohnElkies
