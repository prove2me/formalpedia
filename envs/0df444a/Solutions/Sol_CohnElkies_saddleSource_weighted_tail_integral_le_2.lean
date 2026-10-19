-- Prove2me | solution 2 for CohnElkies.saddleSource_weighted_tail_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:02:05.250033+00:00
-- url     : https://prove2.me/submissions/d52c114a-3d1b-4165-a2da-a8e1c09c515a

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {F : ℝ → ℂ} {W : ℝ → ℝ} {C A R : ℝ}
    (hF : Integrable F)
    (hW : Integrable W)
    (hpoint : ∀ T ∈ saddleGaussianTailSet R,
      ‖F T‖ ≤ (C * A) * W T) :
    (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) ≤
      C * A * (∫ T : ℝ in saddleGaussianTailSet R, W T) := by
  rw [← integral_const_mul]
  refine setIntegral_mono_on hF.norm.integrableOn (hW.integrableOn.const_mul _) ?_ hpoint
  exact (measurableSet_le measurable_const measurable_id.abs)

