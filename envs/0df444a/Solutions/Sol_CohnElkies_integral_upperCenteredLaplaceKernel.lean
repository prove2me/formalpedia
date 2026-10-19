-- Prove2me | solution 1 for CohnElkies.integral_upperCenteredLaplaceKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/12336072-689a-4f9c-b5d8-06478abcbe80

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_complexLaplaceKernel_integrable
import Theorems.Thm_CohnElkies_integral_complexLaplaceKernel
import Theorems.Thm_CohnElkies_complexFrullaniKernel_integrable
import Theorems.Thm_CohnElkies_integral_complexFrullaniKernel
import Theorems.Thm_CohnElkies_upperCenteredLaplaceKernel_eq_frullani_sub_laplace

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {c : ℝ} (hc : 0 < c) (T : ℝ) :
    (∫ a : ℝ in Ioi 0,
      upperCenteredLaplaceKernel c T a) =
      Complex.log (c : ℂ) -
        Complex.log ((c : ℂ) - Complex.I * (T : ℂ)) -
          Complex.I * (T : ℂ) * (c : ℂ)⁻¹ := by
  let z : ℂ := (c : ℂ) - Complex.I * (T : ℂ)
  let w : ℂ := (c : ℂ)
  have hz : 0 < z.re := by simpa [z] using! hc
  have hw : 0 < w.re := by simpa [w] using! hc
  have hfrullani := complexFrullaniKernel_integrable hz hw
  have hlaplace := complexLaplaceKernel_integrable hw
  calc
    (∫ a : ℝ in Ioi 0,
      upperCenteredLaplaceKernel c T a) =
        ∫ a : ℝ in Ioi 0,
          (complexFrullaniKernel z w a -
            Complex.I * (T : ℂ) *
              Complex.exp (-w * (a : ℂ))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro a ha
      exact upperCenteredLaplaceKernel_eq_frullani_sub_laplace
        c T ha.ne'
    _ = (∫ a : ℝ in Ioi 0,
          complexFrullaniKernel z w a) -
        Complex.I * (T : ℂ) *
          (∫ a : ℝ in Ioi 0,
            Complex.exp (-w * (a : ℂ))) := by
      rw [integral_sub hfrullani
        (hlaplace.const_mul (Complex.I * (T : ℂ))),
        integral_const_mul]
    _ = Complex.log (c : ℂ) -
        Complex.log ((c : ℂ) - Complex.I * (T : ℂ)) -
          Complex.I * (T : ℂ) * (c : ℂ)⁻¹ := by
      rw [integral_complexFrullaniKernel hz hw,
        integral_complexLaplaceKernel hw]
end CohnElkies
