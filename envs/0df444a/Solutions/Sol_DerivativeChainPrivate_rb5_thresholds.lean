-- Prove2me | solution 1 for DerivativeChainPrivate.rb5_thresholds
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-18T01:56:36.194866+00:00
-- url     : https://prove2.me/submissions/e4250cf7-c9b1-4ca8-bf60-4110b8018f26

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (N c : ℝ) (hc : 0 ≤ c) :
    (10 ≤ N → c ≤ 4 → 1 + Real.sqrt (1 + c ^ 2 / (N - c)) < 3) ∧
    (13 ≤ N → c ≤ 6 → 1 + Real.sqrt (1 + c ^ 2 / (N - c)) < (7 : ℝ) / 2) ∧
    (17 ≤ N → c ≤ 8 → 1 + Real.sqrt (1 + c ^ 2 / (N - c)) < 4) := by
  constructor
  · intro hN hc4
    have hd : 0 < N - c := by linarith
    have hratio : c ^ 2 / (N - c) < 3 := by
      apply (div_lt_iff₀ hd).mpr
      nlinarith
    have hfrac : 1 + c ^ 2 / (N - c) < 2 ^ 2 := by
      linarith
    have hs := (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)).mpr hfrac
    linarith
  constructor
  · intro hN hc6
    have hd : 0 < N - c := by linarith
    have hratio : c ^ 2 / (N - c) < (21 : ℝ) / 4 := by
      apply (div_lt_iff₀ hd).mpr
      nlinarith
    have hfrac : 1 + c ^ 2 / (N - c) < ((5 : ℝ) / 2) ^ 2 := by
      linarith
    have hs := (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 5 / 2)).mpr hfrac
    linarith
  · intro hN hc8
    have hd : 0 < N - c := by linarith
    have hratio : c ^ 2 / (N - c) < 8 := by
      apply (div_lt_iff₀ hd).mpr
      nlinarith
    have hfrac : 1 + c ^ 2 / (N - c) < 3 ^ 2 := by
      linarith
    have hs := (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3)).mpr hfrac
    linarith
