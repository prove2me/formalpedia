-- Prove2me | solution 1 for CohnElkies.upperFirstBranchSaddleDamping_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/bb8afbf7-cb62-4811-8846-6abae937acca

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperFirstBranch_shortDamping_le_gamma
import Theorems.Thm_CohnElkies_positiveShellDamping_nonneg

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a)
    (T : ℝ) :
    4 * ε * upperGammaDamping ℓ (1 + u) T ≤
      upperFirstBranchSaddleDamping ε ℓ u T := by
  have hshort := upperFirstBranch_shortDamping_le_gamma
    hε hεsmall hℓ hulower huupper horder hmargin T
  have hpositive := positiveShellDamping_nonneg
    (ε := ε) (δ := u - 1) (T := T) hℓ.le
  unfold upperFirstBranchSaddleDamping
  nlinarith
end CohnElkies
