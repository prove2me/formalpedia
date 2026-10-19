-- Prove2me | solution 1 for CohnElkies.eventually_plusSaddleProfile_re_pos_on_star_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/45ccf00e-6036-4a25-b237-2f453af3d541

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half_on_star
import Theorems.Thm_CohnElkies_plusSaddleProfile_re_pos_of_relative_residue_bounds
import Theorems.Thm_CohnElkies_eventually_plusSaddleTaylorRemainder_relative_lt_half_on_star

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a) :
    ∀ᶠ d : ℕ in atTop,
      ∀ r : ℝ, 0 ≤ r → r ≤ saddleSmallRadiusStar ε d →
        0 < (plusSaddleProfile ε ((d : ℝ) / 2) r).re := by
  have hfinite :=
    eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half_on_star
      hε horder
  have hremainder :=
    eventually_plusSaddleTaylorRemainder_relative_lt_half_on_star
      hε hεsmall horder hmargin
  filter_upwards [hfinite, hremainder,
    eventually_gt_atTop (0 : ℕ)] with d hfinite_d hrem_d hd
  intro r hr hrstar
  by_cases hzero : r = 0
  · subst r
    simpa [plusSaddleProfile] using!
      (saddleOriginValue_pos hε ((d : ℝ) / 2))
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hzero)
    have hℓ : 0 < (d : ℝ) / 2 := by positivity
    exact plusSaddleProfile_re_pos_of_relative_residue_bounds
      hε hℓ horder hrpos
      (saddleSmallResidueTruncation ((d : ℝ) / 2))
      (by simpa using! hfinite_d r hr hrstar)
      (by simpa using! hrem_d r hrpos hrstar)
end CohnElkies
