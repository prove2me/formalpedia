-- Prove2me | solution 1 for CohnElkies.integral_poissonLogistic_lowerEndpointPhase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/661e1f31-a28e-4b8f-8efa-c7bdf3893927

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_poissonLogisticDensity_integrable
import Theorems.Thm_CohnElkies_integral_poissonLogisticDensity
import Theorems.Thm_CohnElkies_integral_poissonLogistic_one_add_lowerEndpointPhase
import Theorems.Thm_CohnElkies_poissonLogistic_lowerEndpointPhase_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution :
    (∫ u : ℝ,
      poissonLogisticDensity u *
        lowerEndpointPhase (2 * u)) =
          Real.log (Real.pi / 2) - 1 := by
  have hsplit :
      (∫ u : ℝ,
        poissonLogisticDensity u *
          (1 + lowerEndpointPhase (2 * u))) =
        (∫ u : ℝ, poissonLogisticDensity u) +
          ∫ u : ℝ,
            poissonLogisticDensity u *
              lowerEndpointPhase (2 * u) := by
    calc
      (∫ u : ℝ,
        poissonLogisticDensity u *
          (1 + lowerEndpointPhase (2 * u))) =
          ∫ u : ℝ,
            poissonLogisticDensity u +
              poissonLogisticDensity u *
                lowerEndpointPhase (2 * u) := by
        apply integral_congr_ae
        filter_upwards [] with u
        ring
      _ = (∫ u : ℝ, poissonLogisticDensity u) +
            ∫ u : ℝ,
              poissonLogisticDensity u *
                lowerEndpointPhase (2 * u) :=
        integral_add poissonLogisticDensity_integrable
          poissonLogistic_lowerEndpointPhase_integrable
  have hwallis :=
    integral_poissonLogistic_one_add_lowerEndpointPhase
  rw [hsplit, integral_poissonLogisticDensity] at hwallis
  linarith
end CohnElkies
