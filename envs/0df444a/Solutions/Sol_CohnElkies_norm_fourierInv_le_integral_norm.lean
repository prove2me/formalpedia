-- Prove2me | solution 1 for CohnElkies.norm_fourierInv_le_integral_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/390b3ede-7c84-4fcf-a3a8-9cedfec89a23

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution (F : ℝ → ℂ) (v : ℝ) :
    ‖((𝓕⁻ F : ℝ → ℂ) v)‖ ≤ ∫ s : ℝ, ‖F s‖ := by
  exact VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (-innerₗ ℝ) F v
end CohnElkies
