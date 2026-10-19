-- Prove2me | solution 1 for CohnElkies.saddleSourceNormalizedEnvelope_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/c190106e-16ce-4ff7-a426-6f3d70ebbbce

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceContourEnvelopeScale_pos
import Theorems.Thm_CohnElkies_saddleSourceContour_mellinEnvelope_norm

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
    (T : ℝ) :
    ‖saddleSourceNormalizedEnvelope ε ℓ u T‖ =
      Real.exp (-saddleSourceContourDamping ε ℓ u T) := by
  unfold saddleSourceNormalizedEnvelope
  rw [norm_div,
    saddleSourceContour_mellinEnvelope_norm
      hε hℓ hu horder T,
    Complex.norm_of_nonneg
      (saddleSourceContourEnvelopeScale_pos
        (ε := ε) hℓ hu).le,
    mul_div_cancel_left₀ _
      (saddleSourceContourEnvelopeScale_pos
        (ε := ε) hℓ hu).ne']
end CohnElkies
