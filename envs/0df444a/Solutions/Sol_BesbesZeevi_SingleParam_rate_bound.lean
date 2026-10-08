-- Prove2me | solution 1 for BesbesZeevi.SingleParam.rate_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:51:23.002171+00:00
-- url     : https://prove2.me/submissions/509d859a-ae97-4672-8502-b45ed94046f7

import Mathlib
import Definitions.Def_BesbesZeevi_SingleParam_Tuning

open BesbesZeevi.SingleParam in
theorem solution (n : ℕ) (hn : 8 ≤ n) :
    (n : ℝ) ^ (aCoef (numStages n) - 1) ≤ Real.exp 1 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hn8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  set x := Real.log (n : ℝ) with hxdef
  have hx1 : 1 < x := by
    rw [hxdef, Real.lt_log_iff_exp_lt hnpos]
    have := Real.exp_one_lt_d9
    linarith
  set L := numStages n with hLdef
  have hlogb_le : Real.logb 2 x ≤ (L : ℝ) := by
    rw [hLdef]; unfold numStages; exact Nat.le_ceil _
  have hlogb_pos : 0 < Real.logb 2 x := Real.logb_pos (by norm_num) hx1
  have hL1 : 1 ≤ L := by
    rw [hLdef]; unfold numStages
    exact Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr hlogb_pos))
  have hxle : x ≤ (2 : ℝ) ^ L := by
    have h1 : (2 : ℝ) ^ (Real.logb 2 x) = x := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
    have h2 : (2 : ℝ) ^ (Real.logb 2 x) ≤ (2 : ℝ) ^ (L : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hlogb_le
    rw [h1, Real.rpow_natCast] at h2
    exact h2
  set M : ℝ := (2 : ℝ) ^ (L - 1) with hMdef
  have hM1 : 1 ≤ M := one_le_pow₀ (by norm_num)
  have h2L : (2 : ℝ) ^ L = 2 * M := by
    rw [hMdef, ← pow_succ']
    congr 1; omega
  have ha : aCoef L = M / (2 * M - 1) := by
    unfold aCoef; rw [h2L]
  have hden : 0 < 2 * M - 1 := by linarith
  have key : x * (aCoef L - 1) ≤ 1 + x * (-(1 / 2 : ℝ)) := by
    rw [ha]
    have hx2 : x ≤ 2 * M := by rw [← h2L]; exact hxle
    rw [div_sub_one hden.ne', mul_div_assoc']
    rw [div_le_iff₀ hden]
    nlinarith
  rw [Real.rpow_def_of_pos hnpos, Real.rpow_def_of_pos hnpos, ← Real.exp_add]
  exact Real.exp_le_exp.mpr key
