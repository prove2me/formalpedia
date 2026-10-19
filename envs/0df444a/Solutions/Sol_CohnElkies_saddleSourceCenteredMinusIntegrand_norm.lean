-- Prove2me | solution 1 for CohnElkies.saddleSourceCenteredMinusIntegrand_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/6ce2da13-d7c7-479d-90f5-dbfaf5695391

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceCenteredEnvelope_norm

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
    ‖saddleSourceCenteredMinusIntegrand ε ℓ u v T‖ =
      Real.exp (-saddleSourceContourDamping ε ℓ u T) *
        ‖minusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ))‖ := by
  unfold saddleSourceCenteredMinusIntegrand
  rw [norm_mul,
    saddleSourceCenteredEnvelope_norm hε hℓ hu horder]
end CohnElkies
