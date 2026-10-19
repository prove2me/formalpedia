-- Prove2me | solution 1 for CohnElkies.lowerGammaScaledPositivePart_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/b524beae-bdc5-438d-b3f9-4b370d091ac0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerCoth_log_abs_integrable
import Theorems.Thm_CohnElkies_lower_positiveLogRatio_integrable
import Theorems.Thm_CohnElkies_lowerGammaScaledPositivePart_le
import Theorems.Thm_CohnElkies_lowerGammaScaledPositivePart_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : 0 < c) :
    (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y) ≤
      ((d : ℝ) / 2) *
        (∫ Y : ℝ, max (Real.log
          (4 * Real.pi * c ^ 2 / |Y|)) 0) +
        (1 / 2 : ℝ) *
          (∫ Y : ℝ,
            Real.log (lowerCoth (Real.pi * |Y| / 2))) := by
  have hA : 0 < 4 * Real.pi * c ^ 2 := by positivity
  have hpositive := lower_positiveLogRatio_integrable hA
  have hcoth := lowerCoth_log_abs_integrable
  have hmajor : Integrable (fun Y : ℝ =>
      ((d : ℝ) / 2) *
        max (Real.log (4 * Real.pi * c ^ 2 / |Y|)) 0 +
        (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * |Y| / 2))) :=
    (hpositive.const_mul ((d : ℝ) / 2)).add
      (hcoth.const_mul (1 / 2 : ℝ))
  calc
    (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y) ≤
        ∫ Y : ℝ,
          (((d : ℝ) / 2) *
            max (Real.log (4 * Real.pi * c ^ 2 / |Y|)) 0 +
            (1 / 2 : ℝ) *
              Real.log (lowerCoth (Real.pi * |Y| / 2))) := by
      apply integral_mono_ae
        (lowerGammaScaledPositivePart_integrable hd hc) hmajor
      filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0]
        with Y hY
      exact lowerGammaScaledPositivePart_le hd hc hY
    _ = ((d : ℝ) / 2) *
        (∫ Y : ℝ, max (Real.log
          (4 * Real.pi * c ^ 2 / |Y|)) 0) +
        (1 / 2 : ℝ) *
          (∫ Y : ℝ,
            Real.log (lowerCoth (Real.pi * |Y| / 2))) := by
      rw [integral_add
        (hpositive.const_mul ((d : ℝ) / 2))
        (hcoth.const_mul (1 / 2 : ℝ)),
        integral_const_mul, integral_const_mul]
end CohnElkies
