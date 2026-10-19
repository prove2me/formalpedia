-- Prove2me | solution 1 for CohnElkies.saddleSourceGaussianPlusIntegrand_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/21609e3e-2145-4f98-9f5d-9525fb43cd13

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceGaussianKernel_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u) :
    Integrable (saddleSourceGaussianPlusIntegrand ε ℓ u) := by
  unfold saddleSourceGaussianPlusIntegrand
  exact (saddleSourceGaussianKernel_integrable hℓ hV).ofReal.mul_const _
end CohnElkies
