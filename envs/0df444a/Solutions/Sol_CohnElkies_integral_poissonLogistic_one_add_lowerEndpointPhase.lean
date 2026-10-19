-- Prove2me | solution 1 for CohnElkies.integral_poissonLogistic_one_add_lowerEndpointPhase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/7deb0120-5124-4368-8375-16aac568f5b9

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_poissonLogistic_lowerWallisPhase_product_integrable
import Theorems.Thm_CohnElkies_integral_poissonLogistic_mul_lowerWallisPhaseKernel
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
    (∫ u : ℝ,
      poissonLogisticDensity u *
        (1 + lowerEndpointPhase (2 * u))) =
          Real.log (Real.pi / 2) := by
  calc
    (∫ u : ℝ,
      poissonLogisticDensity u *
        (1 + lowerEndpointPhase (2 * u))) =
        ∫ u : ℝ, ∫ t : ℝ in Ioi 0,
          poissonLogisticDensity u *
            lowerWallisPhaseKernel u t := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [integral_const_mul, integral_lowerWallisPhaseKernel]
    _ = ∫ t : ℝ in Ioi 0, ∫ u : ℝ,
          poissonLogisticDensity u *
            lowerWallisPhaseKernel u t := by
      exact integral_integral_swap
        poissonLogistic_lowerWallisPhase_product_integrable
    _ = ∫ t : ℝ in Ioi 0, wallisLaplaceKernel t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact integral_poissonLogistic_mul_lowerWallisPhaseKernel ht
    _ = Real.log (Real.pi / 2) :=
      integral_wallisLaplaceKernel
end CohnElkies
