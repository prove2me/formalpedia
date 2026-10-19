-- Prove2me | solution 1 for CohnElkies.eventually_plusSaddleProfile_nonneg_on_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/ceb46cd9-0eb8-44d7-b861-1f9d1331045d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_plusSaddleProfile_re_pos_on_star

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ d : ℕ in atTop,
        ∀ r : ℝ, 0 ≤ r → r ≤ saddleSmallRadiusStar ε d →
          0 ≤ (plusSaddleProfile ε ((d : ℝ) / 2) r).re := by
  filter_upwards [eventually_plusSaddleProfile_re_pos_on_star]
    with ε hε
  filter_upwards [hε] with d hd
  intro r hr hstar
  exact (hd r hr hstar).le
end CohnElkies
