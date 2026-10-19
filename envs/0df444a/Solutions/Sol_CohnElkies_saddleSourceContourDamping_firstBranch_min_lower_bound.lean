-- Prove2me | solution 1 for CohnElkies.saddleSourceContourDamping_firstBranch_min_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/33feff2f-d4a5-4419-b6d5-a3ea11acbf86

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaDamping_lower_bound
import Theorems.Thm_CohnElkies_upperFirstBranchSaddleDamping_lower_bound

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
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a)
    (T : ℝ) :
    (ε * ℓ / (2 * Real.exp 1)) *
        min (T ^ 2 / (1 + u)) |T| ≤
      saddleSourceContourDamping ε ℓ u T := by
  have hη : 0 < 1 + u := by linarith
  have hgamma := upperGammaDamping_lower_bound
    hℓ hη T
  have hfirst := upperFirstBranchSaddleDamping_lower_bound
    hε hεsmall hℓ hulower huupper horder hmargin T
  rw [saddleSourceContourDamping_eq_firstBranch]
  calc
    (ε * ℓ / (2 * Real.exp 1)) *
        min (T ^ 2 / (1 + u)) |T| =
      4 * ε *
        ((ℓ / (8 * Real.exp 1)) *
          min (T ^ 2 / (1 + u)) |T|) := by ring
    _ ≤ 4 * ε * upperGammaDamping ℓ (1 + u) T := by
      exact mul_le_mul_of_nonneg_left hgamma (by positivity)
    _ ≤ upperFirstBranchSaddleDamping ε ℓ u T := hfirst
end CohnElkies
