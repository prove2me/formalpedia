-- Prove2me | solution 1 for CohnElkies.limitingPoissonEndpointExpectation_eq_log_pi_div_two_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/e7238af4-5395-4e1a-8c3f-341ea39ddfc0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_poissonLogisticDensity_eq_limitingStripPoissonDensity
import Theorems.Thm_CohnElkies_integral_poissonLogistic_lowerEndpointPhase

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
    limitingPoissonEndpointExpectation =
      Real.log (Real.pi / 2) - 1 := by
  have hscale :
      (∫ u : ℝ,
        limitingStripPoissonDensity (2 * u) *
          lowerEndpointPhase (2 * u)) =
        (1 / 2 : ℝ) * limitingPoissonEndpointExpectation := by
    unfold limitingPoissonEndpointExpectation
    have h := Measure.integral_comp_mul_left
      (fun T : ℝ =>
        limitingStripPoissonDensity T * lowerEndpointPhase T)
      (2 : ℝ)
    simpa [smul_eq_mul,
      abs_of_pos (show (0 : ℝ) < (2 : ℝ)⁻¹ by positivity)] using! h
  have hlogistic :
      (∫ u : ℝ,
        poissonLogisticDensity u *
          lowerEndpointPhase (2 * u)) =
        2 * (∫ u : ℝ,
          limitingStripPoissonDensity (2 * u) *
            lowerEndpointPhase (2 * u)) := by
    calc
      (∫ u : ℝ,
        poissonLogisticDensity u *
          lowerEndpointPhase (2 * u)) =
        ∫ u : ℝ,
          2 * (limitingStripPoissonDensity (2 * u) *
            lowerEndpointPhase (2 * u)) := by
        apply integral_congr_ae
        filter_upwards [] with u
        rw [poissonLogisticDensity_eq_limitingStripPoissonDensity]
        ring
      _ = 2 * (∫ u : ℝ,
          limitingStripPoissonDensity (2 * u) *
            lowerEndpointPhase (2 * u)) := by
        rw [integral_const_mul]
  have hphase := integral_poissonLogistic_lowerEndpointPhase
  linarith
end CohnElkies
