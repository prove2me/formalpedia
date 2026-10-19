-- Prove2me | solution 2 for CohnElkies.saddleSourceGaussianMinusIntegrand_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:09:58.057994+00:00
-- url     : https://prove2.me/submissions/e2307f7d-b6e6-4441-b062-3bd754677d89

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology


theorem solution
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u) :
    Integrable (saddleSourceGaussianMinusIntegrand ε ℓ u) := by
  have hb : 0 < ℓ * saddleSourceGaussianVariance ε ℓ u / 2 := by positivity
  have h := ((integrable_exp_neg_mul_sq hb).ofReal (𝕜 := ℂ)).mul_const
    (minusPolynomial ε (Complex.I * (u : ℂ)))
  refine h.congr (ae_of_all _ (fun T => ?_))
  simp [saddleSourceGaussianMinusIntegrand, saddleSourceGaussianKernel]

