-- Prove2me | solution 1 for CohnElkies.sinc_explicit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/1ed5c1bb-0e5c-4632-93ea-d14b9bdb2b64

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_sinc_abs
import Theorems.Thm_CohnElkies_sinc_quadratic_gap_nonneg
import Theorems.Thm_CohnElkies_abs_sinc_le_twentyfour_twentyfive

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution (T : ℝ) :
    (1 / 25 : ℝ) * min (T ^ 2) 1 ≤
      1 - |Real.sinc (T / 2)| := by
  have hsinc : Real.sinc (T / 2) = Real.sinc (|T| / 2) := by
    rw [← sinc_abs (T / 2)]
    simp [abs_div]
  by_cases hsmall : |T| ≤ 1
  · have hxhalf : |T| / 2 ≤ (1 / 2 : ℝ) := by linarith
    have hgap := sinc_quadratic_gap_nonneg
      (x := |T| / 2) (by positivity) hxhalf
    have hsq : T ^ 2 ≤ (1 : ℝ) := by
      have habsq : |T| ^ 2 ≤ (1 : ℝ) := by
        nlinarith [mul_nonneg (abs_nonneg T) (sub_nonneg.mpr hsmall)]
      simpa only [sq_abs] using! habsq
    have hscaled :
        (4 / 25 : ℝ) * (|T| / 2) ^ 2 =
          (1 / 25 : ℝ) * T ^ 2 := by
      rw [div_pow, sq_abs]
      ring
    rw [min_eq_left hsq, hsinc]
    rwa [← hscaled]
  · have hlarge : 1 ≤ |T| := le_of_not_ge hsmall
    have hsq : (1 : ℝ) ≤ T ^ 2 := by
      have habsq : (1 : ℝ) ≤ |T| ^ 2 := by
        nlinarith [sq_nonneg (|T| - 1)]
      simpa only [sq_abs] using! habsq
    have hgap := abs_sinc_le_twentyfour_twentyfive
      (x := |T| / 2) (by linarith)
    rw [min_eq_right hsq, hsinc]
    linarith
end CohnElkies
