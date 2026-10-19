-- Prove2me | solution 1 for CohnElkies.eventually_plusSaddleProfile_re_pos_on_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/d4c47eb5-6b12-4c74-a101-7e3caf64ac94

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_upper_shortMargin_positive
import Theorems.Thm_CohnElkies_eventually_plusSaddleProfile_re_pos_on_star_fixed

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ d : ℕ in atTop,
        ∀ r : ℝ, 0 ≤ r → r ≤ saddleSmallRadiusStar ε d →
          0 < (plusSaddleProfile ε ((d : ℝ) / 2) r).re := by
  have hsmall :=
    (tendsto_id.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))).eventually
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [self_mem_nhdsWithin, hsmall,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive]
    with ε hε hεsmall horder hmargin
  change 0 < ε at hε
  apply eventually_plusSaddleProfile_re_pos_on_star_fixed
    hε (le_of_lt hεsmall) horder
  intro a ha
  have h := hmargin a ha
  linarith
end CohnElkies
