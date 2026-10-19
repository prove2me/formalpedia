-- Prove2me | solution 1 for CohnElkies.plusSaddleProfile_re_pos_at_sourceSaddle_of_gaussian_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/74a07728-0ce4-4d56-b1f4-0f6a78bb385d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_plusSaddleProfile_exp_re_pos_of_gaussian_error

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ} {d : ℕ} {u : ℝ}
    (hε : 0 < ε) (hd : 0 < d) (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hV : 0 < saddleSourceGaussianVariance ε ((d : ℝ) / 2) u)
    (herror :
      ‖(∫ T : ℝ,
          saddleSourceCenteredPlusIntegrand ε ((d : ℝ) / 2) u
            (saddleLogRadius ε d u) T) -
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand ε ((d : ℝ) / 2) u T)‖ <
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand ε ((d : ℝ) / 2) u T).re) :
    0 < (plusSaddleProfile ε ((d : ℝ) / 2)
      (Real.exp (saddleLogRadius ε d u))).re := by
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  exact plusSaddleProfile_exp_re_pos_of_gaussian_error
    hε hℓ hu horder hV herror
end CohnElkies
