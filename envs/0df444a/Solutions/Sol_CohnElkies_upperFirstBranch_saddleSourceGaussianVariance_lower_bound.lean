-- Prove2me | solution 1 for CohnElkies.upperFirstBranch_saddleSourceGaussianVariance_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/8140f0a7-2afc-490b-b6c2-2642942bdc61

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourcePositiveShellVariance_nonneg
import Theorems.Thm_CohnElkies_upperFirstBranch_shortVariance_le_gamma

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
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a) :
    4 * ε * upperGammaVariance ℓ (1 + u) ≤
      saddleSourceGaussianVariance ε ℓ u := by
  have hshort := upperFirstBranch_shortVariance_le_gamma
    hε hεsmall hℓ hulower huupper horder hmargin
  have hpositive :=
    saddleSourcePositiveShellVariance_nonneg ε (u - 1)
  unfold saddleSourceGaussianVariance
    upperSaddleVariance upperNetShellVariance
  have hη : 2 + (u - 1) = 1 + u := by ring
  rw [hη]
  nlinarith
end CohnElkies
