-- Prove2me | solution 1 for CohnElkies.integral_upperCosLaplaceKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/e8985c7f-f42d-49fc-b43c-022cd3e28106

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_complexFrullaniKernel_integrable
import Theorems.Thm_CohnElkies_integral_complexFrullaniKernel
import Theorems.Thm_CohnElkies_upperCosLaplaceKernel_eq_frullani_re

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
    (∫ a : ℝ in Ioi 0, upperCosLaplaceKernel c T a) =
      Real.log
        (‖((c : ℂ) + Complex.I * (T : ℂ))‖ / c) := by
  let z : ℂ := (c : ℂ)
  let w : ℂ := (c : ℂ) + Complex.I * (T : ℂ)
  have hz : 0 < z.re := by simpa [z] using! hc
  have hw : 0 < w.re := by simpa [w] using! hc
  have hi := complexFrullaniKernel_integrable hz hw
  calc
    (∫ a : ℝ in Ioi 0, upperCosLaplaceKernel c T a) =
        ∫ a : ℝ in Ioi 0, (complexFrullaniKernel z w a).re := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro a ha
      exact upperCosLaplaceKernel_eq_frullani_re c T a
    _ = (∫ a : ℝ in Ioi 0, complexFrullaniKernel z w a).re :=
      integral_re hi
    _ = (Complex.log w - Complex.log z).re := by
      rw [integral_complexFrullaniKernel hz hw]
    _ = Real.log (‖((c : ℂ) + Complex.I * (T : ℂ))‖ / c) := by
      rw [Complex.sub_re, Complex.log_re, Complex.log_re,
        Real.log_div]
      · simp [z, w, abs_of_pos hc]
      · exact (norm_pos_iff.mpr (ne_of_apply_ne Complex.re
          (by simpa [w] using! hc.ne'))).ne'
      · exact hc.ne'
end CohnElkies
