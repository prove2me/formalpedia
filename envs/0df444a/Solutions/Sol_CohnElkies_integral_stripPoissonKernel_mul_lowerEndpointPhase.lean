-- Prove2me | solution 1 for CohnElkies.integral_stripPoissonKernel_mul_lowerEndpointPhase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/09e834ec-fd5e-4294-b975-6633843d1a28

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripBottomMass_pos

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {σ : ℝ} (habove : σ < 1) :
    (∫ T : ℝ, stripPoissonKernel σ T * lowerEndpointPhase T) =
      stripBottomMass σ * lowerPoissonEndpointExpectation σ := by
  have hmass : stripBottomMass σ ≠ 0 :=
    (stripBottomMass_pos habove).ne'
  unfold lowerPoissonEndpointExpectation
    stripNormalizedPoissonKernel
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with T
  field_simp [hmass]
end CohnElkies
