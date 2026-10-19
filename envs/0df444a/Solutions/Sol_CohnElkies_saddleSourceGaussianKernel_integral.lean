-- Prove2me | solution 1 for CohnElkies.saddleSourceGaussianKernel_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/515378a0-8781-4b8f-90f0-8b2ed003cf6d

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
namespace CohnElkies
theorem _root_.solution
    (ε ℓ u : ℝ) :
    (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) =
      Real.sqrt
        (Real.pi /
          (ℓ * saddleSourceGaussianVariance ε ℓ u / 2)) := by
  exact integral_gaussian
    (ℓ * saddleSourceGaussianVariance ε ℓ u / 2)
end CohnElkies
