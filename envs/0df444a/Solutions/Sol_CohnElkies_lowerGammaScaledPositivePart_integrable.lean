-- Prove2me | solution 1 for CohnElkies.lowerGammaScaledPositivePart_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/13f962db-01e1-43a8-8834-cb3790c4f79e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_measurable
import Theorems.Thm_CohnElkies_lowerCoth_log_abs_integrable
import Theorems.Thm_CohnElkies_lower_positiveLogRatio_integrable
import Theorems.Thm_CohnElkies_lowerGammaScaledPositivePart_le

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
    Integrable (lowerGammaScaledPositivePart d c) := by
  have hA : 0 < 4 * Real.pi * c ^ 2 := by positivity
  have hpositive := lower_positiveLogRatio_integrable hA
  have hmajor : Integrable (fun Y : ℝ =>
      ((d : ℝ) / 2) *
        max (Real.log (4 * Real.pi * c ^ 2 / |Y|)) 0 +
        (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * |Y| / 2))) :=
    (hpositive.const_mul ((d : ℝ) / 2)).add
      (lowerCoth_log_abs_integrable.const_mul (1 / 2 : ℝ))
  apply hmajor.mono'
  · have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
    have hℓ : 0 < (d : ℝ) / 2 :=
      half_pos (Nat.cast_pos.mpr hdpos)
    have harg : Measurable (fun Y : ℝ => ((d : ℝ) / 2) * Y) := by
      fun_prop
    have hgamma : Measurable (fun Y : ℝ =>
        lowerGammaBoundaryLog ((d : ℝ) / 2)
          (c * Real.sqrt d) (((d : ℝ) / 2) * Y)) :=
      (lowerGammaBoundaryLog_measurable hℓ
        (c * Real.sqrt d)).comp harg
    exact (hgamma.max measurable_const).aestronglyMeasurable
  · filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0]
      with Y hY
    rw [Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ lowerGammaScaledPositivePart d c Y by
        exact le_max_right _ _)]
    exact lowerGammaScaledPositivePart_le hd hc hY
end CohnElkies
