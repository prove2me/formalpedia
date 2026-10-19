-- Prove2me | solution 1 for CohnElkies.poissonLogistic_lowerEndpointPhase_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/e8e78fb5-fc57-4841-93b5-b458ebc16410

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_poissonLogisticDensity_integrable
import Theorems.Thm_CohnElkies_poissonLogistic_lowerWallisPhase_product_integrable
import Theorems.Thm_CohnElkies_integral_lowerWallisPhaseKernel

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
    Integrable
      (fun u : ℝ =>
        poissonLogisticDensity u *
          lowerEndpointPhase (2 * u)) := by
  have hproduct :=
    poissonLogistic_lowerWallisPhase_product_integrable.integral_prod_left
  have hone :
      Integrable
        (fun u : ℝ =>
          poissonLogisticDensity u *
            (1 + lowerEndpointPhase (2 * u))) := by
    apply hproduct.congr
    filter_upwards [] with u
    rw [integral_const_mul, integral_lowerWallisPhaseKernel]
  have hdifference := hone.sub poissonLogisticDensity_integrable
  apply hdifference.congr
  filter_upwards [] with u
  change
    poissonLogisticDensity u *
        (1 + lowerEndpointPhase (2 * u)) -
      poissonLogisticDensity u =
        poissonLogisticDensity u * lowerEndpointPhase (2 * u)
  ring
end CohnElkies
