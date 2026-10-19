-- Prove2me | solution 1 for CohnElkies.saddleSourceTailIntegrand_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/7f47b780-8512-45b5-88eb-3c35c9b1a6f0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceDampingExponential_continuous

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    Continuous
      (fun T : ℝ =>
        saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) := by
  have hweight : Continuous saddleGaussianTailWeight := by
    unfold saddleGaussianTailWeight
    fun_prop
  exact hweight.mul
    (saddleSourceDampingExponential_continuous
      hε hℓ hu horder)
end CohnElkies
