-- Prove2me | solution 1 for CohnElkies.upperFirstBranch_saddleSourceGaussianVariance_scaled_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/364196ef-5894-4781-bb1e-32470a7ba17d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaVariance_bounds
import Theorems.Thm_CohnElkies_upperFirstBranch_saddleSourceGaussianVariance_lower_bound

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a) :
    2 * ε ≤ (1 + u) *
      saddleSourceGaussianVariance ε ℓ u := by
  have hη : 0 < 1 + u := by linarith
  have hgamma := (upperGammaVariance_bounds hℓ hη).1
  have hsource :=
    upperFirstBranch_saddleSourceGaussianVariance_lower_bound
      hε hεsmall hℓ hulower huupper horder hmargin
  calc
    2 * ε =
        (1 + u) * (4 * ε * (1 / (2 * (1 + u)))) := by
      field_simp [hη.ne']
      norm_num
    _ ≤ (1 + u) *
        (4 * ε * upperGammaVariance ℓ (1 + u)) := by
      gcongr
    _ ≤ (1 + u) *
        saddleSourceGaussianVariance ε ℓ u := by
      gcongr
end CohnElkies
