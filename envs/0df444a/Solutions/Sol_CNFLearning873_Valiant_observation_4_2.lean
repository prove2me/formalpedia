-- Prove2me | solution 1 for CNFLearning873.Valiant.observation_4_2
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T05:23:38.393423+00:00
-- url     : https://prove2.me/submissions/a2b7f39d-e1fb-493e-9f7d-7eb101b6f6c1

import Definitions.Def_CNFLearning873_Valiant_Thresholds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

open CNFLearning873.Valiant

private theorem logTangent {x : ℝ} (hx : 0 < x) (m : ℕ) :
    log₂ x - m ≤ (x / (2 : ℝ)^m - 1) / Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx (pow_pos (by norm_num : 0 < (2 : ℝ)) m))
  rw [Real.log_div hx.ne' (by positivity), Real.log_pow] at h
  apply (le_div_iff₀ (Real.log_pos (by norm_num : 1 < (2 : ℝ)))).mpr
  simpa only [log₂, sub_mul, div_mul_cancel₀ _ (Real.log_pos (by norm_num : 1 < (2 : ℝ))).ne'] using h

private theorem logAbove {x : ℝ} (hx : 0 < x) (m : ℕ) (hm : (2 : ℝ)^m ≤ x) :
    log₂ x ≤ m + 3/2 * (x / (2 : ℝ)^m - 1) := by
  have hq : 0 ≤ x / (2 : ℝ)^m - 1 := by
    rw [sub_nonneg, le_div_iff₀ (by positivity)]
    simpa using hm
  have hl : (2/3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hh : (x / (2 : ℝ)^m - 1) / Real.log 2 ≤ 3/2 * (x / (2 : ℝ)^m - 1) := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
    nlinarith only [mul_nonneg hq (sub_nonneg.mpr hl)]
  linarith only [logTangent hx m, hh]

private theorem logBelow {x : ℝ} (hx : 0 < x) (m : ℕ) (hm : x ≤ (2 : ℝ)^m) :
    log₂ x ≤ m + (x / (2 : ℝ)^m - 1) := by
  have hq : x / (2 : ℝ)^m ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    simpa using hm
  have hl : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hh : (x / (2 : ℝ)^m - 1) / Real.log 2 ≤ x / (2 : ℝ)^m - 1 := by
    apply (div_le_iff₀ (Real.log_pos (by norm_num : 1 < (2 : ℝ)))).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hl)]
  linarith only [logTangent hx m, hh]

theorem solution (k d : ℕ) (t : ℝ) (hk : 100 ≤ k) (hd : 1 ≤ d)
    (ht : 1 ≤ t) (hLLL : LLLCondition k d t) :
    log₂ ((d : ℝ) * k) < (k : ℝ) - log₂ k - 6 ∧
    log₂ ((d : ℝ) * k) ≤ (k : ℝ) * t / (1 + t) - 3 ∧
    (d : ℝ) * k * (2 : ℝ) ^ (1 - (k : ℝ) * t / (1 + t)) ≤ 1 / 4 := by
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ht' : 0 < t := by linarith
  have hkpos : 0 < (k : ℝ) := by linarith
  have hdpos : 0 < (d : ℝ) := by linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul : log₂ ((d : ℝ) * k) = log₂ d + log₂ k := by
    simp only [log₂, Real.log_mul hdpos.ne' hkpos.ne', add_div]
  have hd0 : 0 ≤ log₂ d := div_nonneg (Real.log_nonneg hd') hlog.le
  have hk6 : (6 : ℝ) ≤ log₂ k := by
    change 6 ≤ Real.log k / Real.log 2
    rw [le_div_iff₀ hlog]
    have hh := Real.log_le_log (by positivity : 0 < (2 : ℝ)^6)
      (by norm_num; linarith : (2 : ℝ)^6 ≤ k)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hk8 := logAbove hkpos 6 (by norm_num; linarith)
  norm_num at hk8
  have hlarge (h : 8 ≤ t) : 3 * log₂ t ≤ 9 + 9/16 * (t - 8) := by
    have H := logAbove ht' 3 (by norm_num; linarith)
    norm_num at H
    linarith
  have huv : 3 * log₂ t ≤ t + 3 := by
    by_cases h4 : t ≤ 4
    · have H := logBelow ht' 2 (by norm_num; linarith)
      norm_num at H
      linarith
    · by_cases h8 : 8 ≤ t
      · linarith [hlarge h8]
      · have H := logAbove ht' 2 (by norm_num; linarith)
        norm_num at H
        linarith
  have hcore : log₂ d + log₂ d / t + 2 * log₂ k + t - 3 * log₂ t + 5 ≤ k := by
    convert hLLL using 1
    unfold LLLCondition
    ring
  have hfirst : log₂ d + log₂ k < k - log₂ k - 6 := by
    by_cases h16 : 16 ≤ t
    · have H := hlarge (by linarith)
      linarith [div_nonneg hd0 ht'.le]
    · by_cases h64 : 64 ≤ log₂ d
      · have H : 4 < log₂ d / t := (lt_div_iff₀ ht').mpr (by linarith)
        linarith
      · linarith
  have hpoly := mul_le_mul_of_nonneg_right hcore ht'.le
  simp only [add_mul, sub_mul, div_mul_cancel₀ _ ht'.ne'] at hpoly
  have hcomp : (t - 1) * log₂ k + t * (t - 3 * log₂ t + 2) - 3 ≥ 0 := by
    have h6 := mul_le_mul_of_nonneg_left hk6 (sub_nonneg.mpr ht)
    by_cases h2 : 2 ≤ t
    · nlinarith only [h6, mul_le_mul_of_nonneg_left huv ht'.le, h2]
    · have H := logAbove ht' 0 (by simpa using ht)
      norm_num at H
      nlinarith only [h6, mul_le_mul_of_nonneg_left H ht'.le,
        mul_nonneg (sub_nonneg.mpr ht) (show 0 ≤ 9 - 7/2 * t by linarith)]
  have hsecond : log₂ d + log₂ k ≤ k * t / (1 + t) - 3 := by
    rw [le_sub_iff_add_le, le_div_iff₀ (by linarith)]
    nlinarith only [hpoly, hcomp]
  refine ⟨hmul ▸ hfirst, hmul ▸ hsecond, ?_⟩
  have hpow : (2 : ℝ) ^ log₂ ((d : ℝ) * k) = (d : ℝ) * k :=
    Real.rpow_logb (by norm_num) (by norm_num) (mul_pos hdpos hkpos)
  calc
    _ = (2 : ℝ) ^ (log₂ ((d : ℝ) * k) + (1 - (k : ℝ) * t / (1 + t))) := by
      rw [Real.rpow_add (by norm_num : 0 < (2 : ℝ)), hpow]
    _ ≤ (2 : ℝ) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      rw [hmul]; linarith)
    _ = _ := by norm_num
