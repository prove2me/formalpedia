-- Prove2me | solution 1 for CohnElkies.integral_complexFrullaniKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/caf2c60c-f06e-4da6-92f8-fb6a84176c55

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_integral_complexLaplaceKernel
import Theorems.Thm_CohnElkies_complexFrullaniSegment_re_pos
import Theorems.Thm_CohnElkies_intervalIntegral_complexLaplaceSegment
import Theorems.Thm_CohnElkies_complexFrullaniParameter_integrable
import Theorems.Thm_CohnElkies_intervalIntegral_complexFrullaniLogDerivative

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
    {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    (∫ x : ℝ in Ioi 0, complexFrullaniKernel z w x) =
      Complex.log w - Complex.log z := by
  calc
    (∫ x : ℝ in Ioi 0, complexFrullaniKernel z w x) =
      ∫ x : ℝ in Ioi 0,
        ∫ s in (0 : ℝ)..1,
          (w - z) *
            Complex.exp
              (-complexFrullaniSegment z w s * (x : ℂ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact
        (intervalIntegral_complexLaplaceSegment z w
          (ne_of_gt hx)).symm
    _ = ∫ s in (0 : ℝ)..1,
          ∫ x : ℝ in Ioi 0,
            (w - z) *
              Complex.exp
                (-complexFrullaniSegment z w s * (x : ℂ)) :=
      (intervalIntegral_integral_swap
        (complexFrullaniParameter_integrable hz hw)).symm
    _ = ∫ s in (0 : ℝ)..1,
          (w - z) * (complexFrullaniSegment z w s)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
      change
        (∫ x : ℝ in Ioi 0,
          (w - z) *
            Complex.exp
              (-complexFrullaniSegment z w s * (x : ℂ))) =
          (w - z) * (complexFrullaniSegment z w s)⁻¹
      rw [integral_const_mul,
        integral_complexLaplaceKernel
          (complexFrullaniSegment_re_pos hz hw hs)]
    _ = Complex.log w - Complex.log z :=
      intervalIntegral_complexFrullaniLogDerivative hz hw
end CohnElkies
