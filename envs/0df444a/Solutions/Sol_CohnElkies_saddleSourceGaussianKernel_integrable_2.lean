-- Prove2me | solution 2 for CohnElkies.saddleSourceGaussianKernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:18:04.207679+00:00
-- url     : https://prove2.me/submissions/3e848d5a-8f12-46aa-a1e0-f2380f71fbae

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
    Integrable (saddleSourceGaussianKernel ε ℓ u) := by
  unfold saddleSourceGaussianKernel
  exact integrable_exp_neg_mul_sq (by positivity)

