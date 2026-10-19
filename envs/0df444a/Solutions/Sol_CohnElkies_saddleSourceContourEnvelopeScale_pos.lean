-- Prove2me | solution 1 for CohnElkies.saddleSourceContourEnvelopeScale_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/390474ce-36c8-4935-a754-46b276958319

import Mathlib
import Definitions.Def_SpherePacking

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
    {ε ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : -1 < u) :
    0 < saddleSourceContourEnvelopeScale ε ℓ u := by
  have hη : 0 < 1 + u := by linarith
  unfold saddleSourceContourEnvelopeScale
  exact mul_pos
    (mul_pos (Real.exp_pos _)
      (Real.Gamma_pos_of_pos (by positivity)))
    (Real.exp_pos _)
end CohnElkies
