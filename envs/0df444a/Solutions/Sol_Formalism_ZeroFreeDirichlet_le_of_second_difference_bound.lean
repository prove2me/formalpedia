-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.le_of_second_difference_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:10.768837+00:00
-- url     : https://prove2.me/submissions/7bef90e5-bad1-4210-8e0d-6cffc484023b

import Mathlib
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LeOfSecondDifferenceBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
set_option maxHeartbeats 800000
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {y c₀ C N eY ey h : ℝ} (hy : 2 ≤ y) (hc0 : 0 < c₀) (hc01 : c₀ ≤ 1) (hC : 0 ≤ C)
    (hh : h = Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)))
    (hey0 : 0 ≤ ey) (heY0 : 0 ≤ eY) (hey : ey ≤ h ^ 2) (heY : eY ≤ h ^ 2)
    (hmain : y * h * N ≤ (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h)))
        + 2 * y ^ 2 * h ^ 2 + y * (C * (y * (1 + h)) * eY) + y * (1 + h) * (C * y * ey)) :
    N ≤ (128 / c₀ ^ 2 + 2 + 4 * C) * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y)) := by
  have hy0 : 0 < y := by linarith
  have hc2 : c₀ ^ 2 ≤ 1 := pow_le_one₀ hc0.le hc01
  have hL2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hl2 := Real.log_two_gt_d9
  have hlogmul : Real.log (y * (1 + h)) = Real.log y + Real.log (1 + h) := by
    have hh0' : 0 < h := by rw [hh]; exact Real.exp_pos _
    exact Real.log_mul hy0.ne' (by linarith)
  set L := Real.log y with hLdef
  have hL0 : 0 < L := by linarith
  set s := Real.sqrt L with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = L := Real.sq_sqrt hL0.le
  have hs_half : 1 / 2 ≤ s := by nlinarith
  set g := Real.exp (-(c₀ / 4) * s) with hgdef
  have hg0 : 0 < g := Real.exp_pos _
  have hg1 : g ≤ 1 := by
    rw [hgdef, Real.exp_le_one_iff]
    have : 0 ≤ c₀ / 4 * s := by positivity
    linarith
  have hhg : h = g * g := by
    rw [hh, hgdef, ← Real.exp_add]; congr 1; ring
  have hh0 : 0 < h := by rw [hhg]; positivity
  have hhle : h ≤ g := by rw [hhg]; exact mul_le_of_le_one_left hg0.le hg1
  have hh1 : h ≤ 1 := le_trans hhle hg1
  have hyg : Real.exp (s ^ 2 / 2) ≤ y * g := by
    have hyL : y = Real.exp L := (Real.exp_log hy0).symm
    rw [hgdef, hyL, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc01 hs0, mul_nonneg hs0 (sub_nonneg.mpr hs_half)]
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 2 / 2)
  have hB : L + 1 ≤ 2 * (y * g) := by
    have : 0 ≤ (s ^ 2 / 2) ^ 2 / 2 := by positivity
    linarith
  have ht := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ c₀ / 4 * s by positivity)
  have hgt : g * Real.exp (c₀ / 4 * s) = 1 := by
    rw [hgdef, ← Real.exp_add, show -(c₀ / 4) * s + c₀ / 4 * s = 0 by ring, Real.exp_zero]
  have hA1 : g * (c₀ / 4 * s) ^ 2 ≤ 2 := by
    have h0 : 0 ≤ c₀ / 4 * s := by positivity
    have : (c₀ / 4 * s) ^ 2 ≤ 2 * Real.exp (c₀ / 4 * s) := by linarith
    calc g * (c₀ / 4 * s) ^ 2 ≤ g * (2 * Real.exp (c₀ / 4 * s)) :=
          mul_le_mul_of_nonneg_left this hg0.le
      _ = 2 * (g * Real.exp (c₀ / 4 * s)) := by ring
      _ = 2 := by rw [hgt]; ring
  have hA : c₀ ^ 2 * g * (L + 1) ≤ 33 := by
    have e : c₀ ^ 2 * g * (L + 1) = 16 * (g * (c₀ / 4 * s) ^ 2) + c₀ ^ 2 * g := by
      rw [← hss]; ring
    have : c₀ ^ 2 * g ≤ 1 := mul_le_one₀ hc2 hg0.le hg1
    rw [e]; linarith
  have hA' : g * (L + 1) ≤ 33 / c₀ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have e : g * (L + 1) * c₀ ^ 2 = c₀ ^ 2 * g * (L + 1) := by ring
    rw [e]; exact hA
  have hlog : Real.log (y * (1 + h)) ≤ L + 1 := by
    rw [hlogmul]
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + h)
    linarith
  have hP : 0 < y * h := by positivity
  have hyh1 : y * (1 + h) - y = y * h := by ring
  rw [hyh1] at hmain
  have T1 : (y * h + 1) * ((y * h) * Real.log (y * (1 + h))) ≤ (y * h) * ((y * h + 1) * (L + 1)) := by
    have : (y * h) * Real.log (y * (1 + h)) ≤ (y * h) * (L + 1) :=
      mul_le_mul_of_nonneg_left hlog hP.le
    calc (y * h + 1) * ((y * h) * Real.log (y * (1 + h))) ≤ (y * h + 1) * ((y * h) * (L + 1)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (y * h) * ((y * h + 1) * (L + 1)) := by ring
  have T1' : (y * h + 1) * (L + 1) ≤ (33 / c₀ ^ 2 + 2) * (y * g) := by
    calc (y * h + 1) * (L + 1) = (y * g) * (g * (L + 1)) + (L + 1) := by rw [hhg]; ring
      _ ≤ (y * g) * (33 / c₀ ^ 2) + 2 * (y * g) :=
          add_le_add (mul_le_mul_of_nonneg_left hA' (by positivity)) hB
      _ = (33 / c₀ ^ 2 + 2) * (y * g) := by ring
  have T2 : 2 * y ^ 2 * h ^ 2 ≤ (y * h) * (2 * (y * g)) := by
    have : y * h ≤ y * g := mul_le_mul_of_nonneg_left hhle hy0.le
    calc 2 * y ^ 2 * h ^ 2 = (y * h) * (2 * (y * h)) := by ring
      _ ≤ (y * h) * (2 * (y * g)) := mul_le_mul_of_nonneg_left (by linarith) hP.le
  have hhh : (1 + h) * h ≤ 2 * g := by
    have h1 : h * h ≤ h := mul_le_of_le_one_left hh0.le hh1
    have e : (1 + h) * h = h + h * h := by ring
    rw [e]; linarith
  have hCy : 0 ≤ C * y := mul_nonneg hC hy0.le
  have T3 : y * (C * (y * (1 + h)) * eY) ≤ (y * h) * (2 * C * (y * g)) := by
    have hk : 0 ≤ C * (y * (1 + h)) := mul_nonneg hC (by positivity)
    have : C * (y * (1 + h)) * eY ≤ C * (y * (1 + h)) * h ^ 2 := mul_le_mul_of_nonneg_left heY hk
    calc y * (C * (y * (1 + h)) * eY) ≤ y * (C * (y * (1 + h)) * h ^ 2) :=
          mul_le_mul_of_nonneg_left this hy0.le
      _ = (y * h) * (C * y * ((1 + h) * h)) := by ring
      _ ≤ (y * h) * (C * y * (2 * g)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhh hCy) hP.le
      _ = (y * h) * (2 * C * (y * g)) := by ring
  have T4 : y * (1 + h) * (C * y * ey) ≤ (y * h) * (2 * C * (y * g)) := by
    have hk : 0 ≤ y * (1 + h) * (C * y) := mul_nonneg (by positivity) hCy
    have : y * (1 + h) * (C * y) * ey ≤ y * (1 + h) * (C * y) * h ^ 2 :=
      mul_le_mul_of_nonneg_left hey hk
    calc y * (1 + h) * (C * y * ey) = y * (1 + h) * (C * y) * ey := by ring
      _ ≤ y * (1 + h) * (C * y) * h ^ 2 := this
      _ = (y * h) * (C * y * ((1 + h) * h)) := by ring
      _ ≤ (y * h) * (C * y * (2 * g)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhh hCy) hP.le
      _ = (y * h) * (2 * C * (y * g)) := by ring
  have T1'' := mul_le_mul_of_nonneg_left T1' hP.le
  have hfin : (33 / c₀ ^ 2 + 2) * (y * g) + 2 * (y * g) + 2 * C * (y * g) + 2 * C * (y * g) ≤
      (128 / c₀ ^ 2 + 2 + 4 * C) * y * g := by
    have h95 : 2 ≤ 95 / c₀ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have := mul_le_mul_of_nonneg_right h95 (by positivity : (0 : ℝ) ≤ y * g)
    have e1 : (128 / c₀ ^ 2 + 2 + 4 * C) * y * g =
        (33 / c₀ ^ 2 + 2) * (y * g) + 95 / c₀ ^ 2 * (y * g) + 2 * C * (y * g) + 2 * C * (y * g) := by
      ring
    rw [e1]; linarith
  have hfin' := mul_le_mul_of_nonneg_left hfin hP.le
  refine le_of_mul_le_mul_left ?_ hP
  linarith
end Formalism.ZeroFreeDirichlet
