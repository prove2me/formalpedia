-- Prove2me | solution 1 for CohnElkies.integral_lowerWallisRegularizedPhaseKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/b5d1f7f4-1bd8-42c4-a1b3-3ec97e649f34

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_complexWallisPhaseKernel_integrable
import Theorems.Thm_CohnElkies_integral_complexWallisPhaseKernel
import Theorems.Thm_CohnElkies_complexWallisPhaseKernel_re

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {a : ℝ} (ha : 0 < a) (u : ℝ) :
    (∫ t : ℝ in Ioi 0,
      lowerWallisRegularizedPhaseKernel a u t) =
      (1 + ((a : ℂ) - Complex.I * (u : ℂ)) *
        Complex.log ((a : ℂ) - Complex.I * (u : ℂ)) -
        (((a : ℂ) - Complex.I * (u : ℂ)) + 1) *
          Complex.log (((a : ℂ) - Complex.I * (u : ℂ)) + 1)).re := by
  let z : ℂ := (a : ℂ) - Complex.I * (u : ℂ)
  have hz : 0 < z.re := by
    try dsimp [z]
    simpa using! ha
  calc
    (∫ t : ℝ in Ioi 0,
      lowerWallisRegularizedPhaseKernel a u t) =
        ∫ t : ℝ in Ioi 0,
          (complexWallisPhaseKernel z t).re := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      exact (complexWallisPhaseKernel_re a u t).symm
    _ = (∫ t : ℝ in Ioi 0,
          complexWallisPhaseKernel z t).re := by
      exact integral_re (complexWallisPhaseKernel_integrable hz)
    _ = (1 + z * Complex.log z -
          (z + 1) * Complex.log (z + 1)).re := by
      rw [integral_complexWallisPhaseKernel hz]
end CohnElkies
