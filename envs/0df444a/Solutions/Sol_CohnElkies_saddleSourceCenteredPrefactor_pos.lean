-- Prove2me | solution 1 for CohnElkies.saddleSourceCenteredPrefactor_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/2f40337b-a344-41df-804a-8eeb878d44ad

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
    (v : ℝ) :
    0 < saddleSourceCenteredPrefactor ε ℓ u v := by
  unfold saddleSourceCenteredPrefactor
  exact mul_pos
    (mul_pos (div_pos hℓ (by positivity))
      (Real.exp_pos _))
    (saddleSourceContourEnvelopeScale_pos
      (ε := ε) hℓ hu)
end CohnElkies
