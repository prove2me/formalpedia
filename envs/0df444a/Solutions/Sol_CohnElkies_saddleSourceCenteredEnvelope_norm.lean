-- Prove2me | solution 1 for CohnElkies.saddleSourceCenteredEnvelope_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/b28bcfd4-b355-4ad5-9a93-33ee66a49460

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceNormalizedEnvelope_norm

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (v T : ℝ) :
    ‖saddleSourceCenteredEnvelope ε ℓ u v T‖ =
      Real.exp (-saddleSourceContourDamping ε ℓ u T) := by
  unfold saddleSourceCenteredEnvelope
  rw [norm_mul,
    saddleSourceNormalizedEnvelope_norm
      hε hℓ hu horder T,
    Complex.norm_exp_I_mul_ofReal, mul_one]
end CohnElkies
