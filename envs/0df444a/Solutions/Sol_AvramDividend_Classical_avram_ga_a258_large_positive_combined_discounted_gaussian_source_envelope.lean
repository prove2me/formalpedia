-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a258_large_positive_combined_discounted_gaussian_source_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:56:37.058084+00:00
-- url     : https://prove2.me/submissions/569dd6f6-0651-4e42-9f60-c9d91ac9359a

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Defs.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (e0 e1 w0 w1 d h r z B T : ℝ)
    (he0 : 0 ≤ e0) (he01 : e0 ≤ 1)
    (he1 : 0 ≤ e1) (he11 : e1 ≤ 1)
    (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hw0 : |w0| ≤ B) (hd : |d| ≤ B) (hh : |h| ≤ B)
    (hw1 : w1 ≤ T) :
    max (e1*(w1-w0)-e0*(d*r+h/2*z^2)) 0 ≤
      T+B*(1+|r|+z^2/2) := by
  have he1w : e1*w1 ≤ T := by
    have hb : e1*w1 ≤ e1*T :=
      mul_le_mul_of_nonneg_left hw1 he1
    have hc : e1*T ≤ T := by
      nlinarith [mul_nonneg (sub_nonneg.mpr he11) hT]
    linarith
  have he1abs : e1*|w0| ≤ B := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he11) (abs_nonneg w0)]
  have hW : -e1*w0 ≤ B := by
    have hp := mul_le_mul_of_nonneg_left (neg_le_abs w0) he1
    nlinarith [he1abs]
  have he0d : e0*|d| ≤ B := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he01) (abs_nonneg d)]
  have hD : -(e0*d*r) ≤ B*|r| := by
    calc
      -(e0*d*r) ≤ |e0*d*r| := neg_le_abs _
      _ = (e0*|d|)*|r| := by
        rw [abs_mul,abs_mul,abs_of_nonneg he0]
      _ ≤ B*|r| :=
        mul_le_mul_of_nonneg_right he0d (abs_nonneg _)
  have he0h : e0*|h| ≤ B := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he01) (abs_nonneg h)]
  have hZ : 0 ≤ z^2 := sq_nonneg _
  have hH : -(e0*h/2*z^2) ≤ (B/2)*z^2 := by
    calc
      -(e0*h/2*z^2) ≤ |e0*h/2*z^2| := neg_le_abs _
      _ = (e0*|h|/2)*z^2 := by
        rw [abs_mul,abs_div,abs_mul,abs_of_nonneg he0,
          abs_of_nonneg hZ,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      _ ≤ (B/2)*z^2 :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right he0h (by norm_num)) hZ
  have hMain : e1*(w1-w0)-e0*(d*r+h/2*z^2) ≤
      T+B*(1+|r|+z^2/2) := by
    nlinarith [he1w,hW,hD,hH]
  apply max_le hMain
  have : 0 ≤ 1+|r|+z^2/2 := by positivity
  positivity
