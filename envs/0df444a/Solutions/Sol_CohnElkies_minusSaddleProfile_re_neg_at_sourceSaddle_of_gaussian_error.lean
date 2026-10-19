-- Prove2me | solution 1 for CohnElkies.minusSaddleProfile_re_neg_at_sourceSaddle_of_gaussian_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/73308e18-ad41-484d-98cc-3de259be832b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_minusSaddleProfile_exp_re_neg_of_gaussian_error

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
          saddleSourceCenteredMinusIntegrand ε ((d : ℝ) / 2) u
            (saddleLogRadius ε d u) T) -
        (∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ((d : ℝ) / 2) u T)‖ <
        -(∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ((d : ℝ) / 2) u T).re) :
    (minusSaddleProfile ε ((d : ℝ) / 2)
      (Real.exp (saddleLogRadius ε d u))).re < 0 := by
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  exact minusSaddleProfile_exp_re_neg_of_gaussian_error
    hε hℓ hu horder hV herror
end CohnElkies
