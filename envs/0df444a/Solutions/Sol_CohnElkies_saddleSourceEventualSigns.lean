-- Prove2me | solution 1 for CohnElkies.saddleSourceEventualSigns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/34b6b780-f7b6-4ee1-ad3f-bbf3df04e17c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_plusSaddleProfile_nonneg_on_star
import Theorems.Thm_CohnElkies_eventually_plusSaddleProfile_nonneg_of_star
import Theorems.Thm_CohnElkies_eventually_minusSaddleProfile_nonpos_of_sourceRadius

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution : SaddleSourceEventualSigns := by
  unfold SaddleSourceEventualSigns
  filter_upwards [eventually_plusSaddleProfile_nonneg_on_star,
    eventually_plusSaddleProfile_nonneg_of_star,
    eventually_minusSaddleProfile_nonpos_of_sourceRadius]
    with ε hsmall hlarge hminus
  filter_upwards [hsmall, hlarge, hminus]
    with d hsmall_d hlarge_d hminus_d
  constructor
  · intro x
    change 0 ≤ (plusSaddleProfile ε ((d : ℝ) / 2) ‖x‖).re
    rcases le_total ‖x‖ (saddleSmallRadiusStar ε d) with hx | hx
    · exact hsmall_d ‖x‖ (norm_nonneg x) hx
    · exact hlarge_d ‖x‖ hx
  · intro x hx
    change (minusSaddleProfile ε ((d : ℝ) / 2) ‖x‖).re ≤ 0
    exact hminus_d ‖x‖ hx
end CohnElkies
