-- Prove2me | solution 1 for CohnElkies.abs_exp_sub_one_le_abs_mul_exp_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/d30f0540-8053-45e6-ac03-fa92cb7b0c6a

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution (t : ℝ) :
    |Real.exp t - 1| ≤ |t| * Real.exp |t| := by
  rcases le_total 0 t with ht | ht
  · have hexp : 1 ≤ Real.exp t := by
      simpa using! Real.exp_le_exp.mpr ht
    rw [abs_of_nonneg (sub_nonneg.mpr hexp),
      abs_of_nonneg ht]
    have hsupport := Real.add_one_le_exp (-t)
    have hmul := mul_le_mul_of_nonneg_left hsupport
      (Real.exp_pos t).le
    have hcancel : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [hcancel] at hmul
    nlinarith
  · have hexp : Real.exp t ≤ 1 := by
      simpa using! Real.exp_le_exp.mpr ht
    have hnegt : 0 ≤ -t := neg_nonneg.mpr ht
    have hexpneg : 1 ≤ Real.exp (-t) := by
      simpa using! Real.exp_le_exp.mpr hnegt
    rw [abs_of_nonpos (sub_nonpos.mpr hexp),
      abs_of_nonpos ht]
    have hsupport := Real.add_one_le_exp t
    have hlinear : 1 - Real.exp t ≤ -t := by
      linarith
    calc
      -(Real.exp t - 1) = 1 - Real.exp t := by ring
      _ ≤ -t := hlinear
      _ ≤ -t * Real.exp (-t) := by
        nlinarith [mul_nonneg hnegt
          (sub_nonneg.mpr hexpneg)]
end CohnElkies
