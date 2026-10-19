-- Prove2me | solution 1 for CohnElkies.saddleSourceContour_envelope_eq_scale_mul_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/8e34a565-cced-469c-bf07-fde299ec4a08

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceContourEnvelopeScale_pos

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
    {ε ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : -1 < u)
    (T : ℝ) :
    saddleMellinEnvelope ε ℓ
        (saddleSourceMellinContour ℓ u T) =
      (saddleSourceContourEnvelopeScale ε ℓ u : ℂ) *
        saddleSourceNormalizedEnvelope ε ℓ u T := by
  unfold saddleSourceNormalizedEnvelope
  have hn : (saddleSourceContourEnvelopeScale ε ℓ u : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (saddleSourceContourEnvelopeScale_pos
        (ε := ε) hℓ hu).ne'
  field_simp [hn]
end CohnElkies
