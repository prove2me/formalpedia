-- Prove2me | solution 1 for CohnElkies.integral_complexWallisPhaseKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/ca49c3b0-74e5-4a06-818d-2cb3e7a20734

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_integral_complexFrullaniKernel
import Theorems.Thm_CohnElkies_complexFrullaniShiftParameter_integrable
import Theorems.Thm_CohnElkies_intervalIntegral_complexFrullaniShift
import Theorems.Thm_CohnElkies_intervalIntegral_complexWallisLog

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {z : ℂ} (hz : 0 < z.re) :
    (∫ x : ℝ in Ioi 0, complexWallisPhaseKernel z x) =
      1 + z * Complex.log z -
        (z + 1) * Complex.log (z + 1) := by
  calc
    (∫ x : ℝ in Ioi 0, complexWallisPhaseKernel z x) =
      ∫ x : ℝ in Ioi 0,
        ∫ s in (0 : ℝ)..1,
          complexFrullaniKernel (z + (s : ℂ)) 1 x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact
        (intervalIntegral_complexFrullaniShift z hx.ne').symm
    _ = ∫ s in (0 : ℝ)..1,
          ∫ x : ℝ in Ioi 0,
            complexFrullaniKernel (z + (s : ℂ)) 1 x :=
      (intervalIntegral_integral_swap
        (complexFrullaniShiftParameter_integrable hz)).symm
    _ = ∫ s in (0 : ℝ)..1,
          -Complex.log (z + (s : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
      have hspositive : 0 < (z + (s : ℂ)).re := by
        simp only [Complex.add_re, Complex.ofReal_re]
        linarith [hs.1]
      change
        (∫ x : ℝ in Ioi 0,
          complexFrullaniKernel (z + (s : ℂ)) 1 x) =
          -Complex.log (z + (s : ℂ))
      rw [integral_complexFrullaniKernel
        hspositive (by norm_num : 0 < (1 : ℂ).re)]
      simp
    _ = -(∫ s in (0 : ℝ)..1,
          Complex.log (z + (s : ℂ))) := by
      rw [intervalIntegral.integral_neg]
    _ = 1 + z * Complex.log z -
        (z + 1) * Complex.log (z + 1) := by
      rw [intervalIntegral_complexWallisLog hz]
      ring
end CohnElkies
