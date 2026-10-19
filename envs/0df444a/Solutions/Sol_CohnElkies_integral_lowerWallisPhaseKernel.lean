-- Prove2me | solution 1 for CohnElkies.integral_lowerWallisPhaseKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/263d1256-dc13-4af4-9280-0ed4d778e31d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_integral_lowerWallisRegularizedPhaseKernel
import Theorems.Thm_CohnElkies_integral_lowerWallisRegularizedPhaseKernel
import Theorems.Thm_CohnElkies_tendsto_lowerWallisComplexLogPhase_regularized

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (u : ℝ) :
    (∫ t : ℝ in Ioi 0, lowerWallisPhaseKernel u t) =
      1 + lowerEndpointPhase (2 * u) := by
  have hdominated :=
    tendsto_integral_lowerWallisRegularizedPhaseKernel u
  have hcomputed :
      Tendsto
        (fun n : ℕ =>
          ∫ t : ℝ in Ioi 0,
            lowerWallisRegularizedPhaseKernel
              (1 / ((n : ℝ) + 1)) u t)
        atTop (𝓝 (1 + lowerEndpointPhase (2 * u))) := by
    have hidentity (n : ℕ) :
        (∫ t : ℝ in Ioi 0,
          lowerWallisRegularizedPhaseKernel
            (1 / ((n : ℝ) + 1)) u t) =
          lowerWallisComplexLogPhase
            (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) -
              Complex.I * (u : ℂ)) := by
      exact integral_lowerWallisRegularizedPhaseKernel
        (by positivity) u
    simp_rw [hidentity]
    exact tendsto_lowerWallisComplexLogPhase_regularized u
  exact tendsto_nhds_unique hdominated hcomputed
end CohnElkies
