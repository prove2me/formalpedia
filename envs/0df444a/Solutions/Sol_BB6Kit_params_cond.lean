-- Prove2me | solution 1 for BB6Kit.params_cond
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T22:30:21.498091+00:00
-- url     : https://prove2.me/submissions/e98deb43-f94f-432a-8788-1ec138c22213

import Mathlib
import Definitions.Def_BB6Kit

namespace BB6KitPC

theorem big1 (n : ℕ) (hn : 60 ≤ n) : 2 ^ 20 * n ^ 2 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h : (m + 1) ^ 2 ≤ 2 * m ^ 2 := by nlinarith
    calc 2 ^ 20 * (m + 1) ^ 2 ≤ 2 * (2 ^ 20 * m ^ 2) := by nlinarith
      _ < 2 * 2 ^ m := by omega
      _ = 2 ^ (m + 1) := by ring

theorem big2 (n : ℕ) (hn : 60 ≤ n) : 8 * n * (1441792 * n ^ 2 + 1) ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h3 : (m + 1) ^ 3 ≤ 2 * m ^ 3 := by nlinarith [sq_nonneg m]
    have e1 : 8 * (m + 1) * (1441792 * (m + 1) ^ 2 + 1) = 11534336 * (m + 1) ^ 3 + 8 * (m + 1) := by ring
    have e2 : 8 * m * (1441792 * m ^ 2 + 1) = 11534336 * m ^ 3 + 8 * m := by ring
    rw [e1]; rw [e2] at ih
    calc 11534336 * (m + 1) ^ 3 + 8 * (m + 1) ≤ 2 * (11534336 * m ^ 3 + 8 * m) := by nlinarith
      _ ≤ 2 * 2 ^ m := by omega
      _ = 2 ^ (m + 1) := by ring

end BB6KitPC

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (hn : 60 ≤ n) :
    3 ≤ BB6Kit.fK n ∧ 5 ≤ BB6Kit.fL n ∧ BB6Kit.fN n ≤ BB6Kit.fR n * BB6Kit.fS n * BB6Kit.fR n ∧
    (0 < BB6Kit.fR1 n ∧ 0 < BB6Kit.fS1 n ∧ 0 < BB6Kit.fR1 n ∧ 0 < BB6Kit.fR2 n ∧ 0 < BB6Kit.fS2 n ∧
      0 < BB6Kit.fR2 n ∧ 0 < BB6Kit.fR3 n ∧ 0 < BB6Kit.fS3 n ∧ 0 < BB6Kit.fR3 n) ∧
    (BB6Kit.fR1 n + BB6Kit.fR2 n + BB6Kit.fR3 n < BB6Kit.fR n ∧
      BB6Kit.fS1 n + BB6Kit.fS2 n + BB6Kit.fS3 n < BB6Kit.fS n ∧
      BB6Kit.fR1 n + BB6Kit.fR2 n + BB6Kit.fR3 n < BB6Kit.fR n) ∧ 0 < BB6Kit.fChi n ∧
    (BB6Kit.fK n : ℝ) *
      (max (max ((BB6Kit.fR1 n : ℝ) + (BB6Kit.fS1 n : ℝ) + 1) ((BB6Kit.fS1 n : ℝ) + (BB6Kit.fR1 n : ℝ) + 1))
        (max ((BB6Kit.fR1 n : ℝ) + (BB6Kit.fR1 n : ℝ) + 1)
          (BB6Kit.fChi n * Real.sqrt (((BB6Kit.fR1 n : ℝ) + 1) * ((BB6Kit.fS1 n : ℝ) + 1) *
            ((BB6Kit.fR1 n : ℝ) + 1))))) <
      ((BB6Kit.fR1 n : ℝ) + 1) * ((BB6Kit.fS1 n : ℝ) + 1) * ((BB6Kit.fR1 n : ℝ) + 1) ∧
    BB6Kit.fL n < (BB6Kit.fR1 n + 1) * (BB6Kit.fS1 n + 1) * (BB6Kit.fR1 n + 1) ∧
    2 * BB6Kit.fK n * BB6Kit.fL n < (BB6Kit.fR2 n + 1) * (BB6Kit.fS2 n + 1) * (BB6Kit.fR2 n + 1) ∧
    BB6Kit.fK n ^ 2 < (BB6Kit.fR2 n + 1) * (BB6Kit.fS2 n + 1) * (BB6Kit.fR2 n + 1) ∧
    3 * BB6Kit.fK n ^ 2 * BB6Kit.fL n < (BB6Kit.fR3 n + 1) * (BB6Kit.fS3 n + 1) * (BB6Kit.fR3 n + 1) ∧
    max (BB6Kit.fR1 n) (BB6Kit.fR2 n) < 2 ^ n ∧ BB6Kit.fL n * BB6Kit.fR n ≤ 2 ^ n ∧
    (BB6Kit.fK n : ℝ) * (BB6Kit.fL n : ℝ) * Real.log 4 ≤ 2 ^ 30 * (((n : ℝ) + 2) * Real.log 2) ^ 3 := by
  have hK : BB6Kit.fK n = 2 ^ 23 * n ^ 2 := rfl
  have hL : BB6Kit.fL n = 8 * n := rfl
  have hR1 : BB6Kit.fR1 n = 2 ^ 20 * n ^ 2 := by
    show 2 ^ 23 * n ^ 2 / 8 = _
    rw [show 2 ^ 23 * n ^ 2 = 2 ^ 20 * n ^ 2 * 8 by ring]; exact Nat.mul_div_cancel _ (by norm_num)
  have hR2 : BB6Kit.fR2 n = 2 ^ 17 * n ^ 2 := by
    show 2 ^ 23 * n ^ 2 / 64 = _
    rw [show 2 ^ 23 * n ^ 2 = 2 ^ 17 * n ^ 2 * 64 by ring]; exact Nat.mul_div_cancel _ (by norm_num)
  have hR3 : BB6Kit.fR3 n = 2 ^ 18 * n ^ 2 := by
    show 2 ^ 23 * n ^ 2 / 32 = _
    rw [show 2 ^ 23 * n ^ 2 = 2 ^ 18 * n ^ 2 * 32 by ring]; exact Nat.mul_div_cancel _ (by norm_num)
  have hS1 : BB6Kit.fS1 n = 80 := rfl
  have hS2 : BB6Kit.fS2 n = 2 ^ 15 * n := rfl
  have hS3 : BB6Kit.fS3 n = 2 ^ 15 * n := rfl
  have hR : BB6Kit.fR n = 1441792 * n ^ 2 + 1 := by
    show BB6Kit.fR1 n + BB6Kit.fR2 n + BB6Kit.fR3 n + 1 = _
    rw [hR1, hR2, hR3]; ring
  have hS : BB6Kit.fS n = 65536 * n + 81 := by
    show BB6Kit.fS1 n + BB6Kit.fS2 n + BB6Kit.fS3 n + 1 = _
    rw [hS1, hS2, hS3]; ring
  have hN : BB6Kit.fN n = 2 ^ 23 * n ^ 2 * (2 ^ 23 * n ^ 2 + 1) * (8 * n) / 2 := by
    unfold BB6Kit.fN; rw [hK, hL]
  have hM0 : BB6Kit.fM0 n = ((2 ^ 20 * n ^ 2 + 1) * 81 * (2 ^ 20 * n ^ 2 + 1) - 1) / (2 ^ 23 * n ^ 2) := by
    show ((BB6Kit.fR1 n + 1) * (BB6Kit.fS1 n + 1) * (BB6Kit.fR1 n + 1) - 1) / BB6Kit.fK n = _
    rw [hR1, hS1, hK]
  have hn1 : 1 ≤ n := by omega
  have hn2 : 3600 ≤ n ^ 2 := by nlinarith
  have hKpos : 0 < 2 ^ 23 * n ^ 2 := by positivity
  -- M0 is large
  have hM0big : 2 ^ 23 * n ^ 2 ≤ BB6Kit.fM0 n := by
    rw [hM0, Nat.le_div_iff_mul_le hKpos]
    have : 2 ^ 23 * n ^ 2 * (2 ^ 23 * n ^ 2) + 1 ≤ (2 ^ 20 * n ^ 2 + 1) * 81 * (2 ^ 20 * n ^ 2 + 1) := by
      nlinarith
    omega
  have hKM0 : 2 ^ 23 * n ^ 2 * BB6Kit.fM0 n < (2 ^ 20 * n ^ 2 + 1) * 81 * (2 ^ 20 * n ^ 2 + 1) := by
    rw [hM0]
    have h1 := Nat.div_mul_le_self ((2 ^ 20 * n ^ 2 + 1) * 81 * (2 ^ 20 * n ^ 2 + 1) - 1) (2 ^ 23 * n ^ 2)
    have h2 : 1 ≤ (2 ^ 20 * n ^ 2 + 1) * 81 * (2 ^ 20 * n ^ 2 + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [mul_comm]
    omega
  -- χ √V1 = M0
  have hV1pos : (0:ℝ) < ((BB6Kit.fR1 n : ℝ) + 1) * ((BB6Kit.fS1 n : ℝ) + 1) * ((BB6Kit.fR1 n : ℝ) + 1) := by
    positivity
  have hchiV : BB6Kit.fChi n * Real.sqrt (((BB6Kit.fR1 n : ℝ) + 1) * ((BB6Kit.fS1 n : ℝ) + 1) *
      ((BB6Kit.fR1 n : ℝ) + 1)) = (BB6Kit.fM0 n : ℝ) := by
    unfold BB6Kit.fChi
    push_cast
    rw [div_mul_cancel₀]
    exact (Real.sqrt_pos.mpr hV1pos).ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hK]; nlinarith
  · rw [hL]; omega
  · rw [hN, hR, hS]
    apply le_trans (Nat.div_le_self _ _)
    have h5 : n ^ 2 * n ^ 2 * n ≤ n ^ 2 * n ^ 2 * n := le_rfl
    nlinarith [pow_pos (by omega : 0 < n) 5]
  · rw [hR1, hS1, hR2, hS2, hR3, hS3]
    refine ⟨by positivity, by norm_num, by positivity, by positivity, by positivity, by positivity,
      by positivity, by positivity, by positivity⟩
  · rw [hR, hS, hR1, hR2, hR3, hS1, hS2, hS3]
    refine ⟨by omega, by omega, by omega⟩
  · unfold BB6Kit.fChi
    apply div_pos
    · have : 0 < BB6Kit.fM0 n := lt_of_lt_of_le hKpos hM0big
      exact_mod_cast this
    · apply Real.sqrt_pos.mpr
      push_cast
      positivity
  · rw [hchiV]
    have hmax : max (max ((BB6Kit.fR1 n : ℝ) + (BB6Kit.fS1 n : ℝ) + 1) ((BB6Kit.fS1 n : ℝ) + (BB6Kit.fR1 n : ℝ) + 1))
        (max ((BB6Kit.fR1 n : ℝ) + (BB6Kit.fR1 n : ℝ) + 1) (BB6Kit.fM0 n : ℝ)) = (BB6Kit.fM0 n : ℝ) := by
      have hb : (BB6Kit.fR1 n : ℝ) + (BB6Kit.fR1 n : ℝ) + 1 ≤ (BB6Kit.fM0 n : ℝ) := by
        have : BB6Kit.fR1 n + BB6Kit.fR1 n + 1 ≤ BB6Kit.fM0 n := by rw [hR1]; nlinarith
        exact_mod_cast this
      have ha : (BB6Kit.fR1 n : ℝ) + (BB6Kit.fS1 n : ℝ) + 1 ≤ (BB6Kit.fM0 n : ℝ) := by
        have : BB6Kit.fR1 n + BB6Kit.fS1 n + 1 ≤ BB6Kit.fM0 n := by rw [hR1, hS1]; nlinarith
        exact_mod_cast this
      have hc : (BB6Kit.fS1 n : ℝ) + (BB6Kit.fR1 n : ℝ) + 1 ≤ (BB6Kit.fM0 n : ℝ) := by linarith
      rw [max_eq_right hb, max_eq_right (max_le ha hc)]
    rw [hmax]
    have : BB6Kit.fK n * BB6Kit.fM0 n < (BB6Kit.fR1 n + 1) * (BB6Kit.fS1 n + 1) * (BB6Kit.fR1 n + 1) := by
      rw [hK, hR1, hS1]; exact hKM0
    have h' : ((BB6Kit.fK n * BB6Kit.fM0 n : ℕ) : ℝ) <
        (((BB6Kit.fR1 n + 1) * (BB6Kit.fS1 n + 1) * (BB6Kit.fR1 n + 1) : ℕ) : ℝ) := Nat.cast_lt.mpr this
    push_cast at h'
    linarith
  · rw [hL, hR1, hS1]; nlinarith
  · rw [hK, hL, hR2, hS2]; nlinarith [pow_pos (by omega : 0 < n) 5]
  · rw [hK, hR2, hS2]; nlinarith [pow_pos (by omega : 0 < n) 5]
  · rw [hK, hL, hR3, hS3]; nlinarith [pow_pos (by omega : 0 < n) 5]
  · rw [hR1, hR2]
    have := BB6KitPC.big1 n hn
    have h2 : 2 ^ 17 * n ^ 2 ≤ 2 ^ 20 * n ^ 2 := by nlinarith
    rw [max_eq_left h2]; exact this
  · rw [hL, hR]; exact BB6KitPC.big2 n hn
  · rw [hK, hL]
    push_cast
    have hl2 := Real.log_two_gt_d9
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [h4]
    have hn0 : (0:ℝ) ≤ n := by positivity
    have hc : (n : ℝ) ^ 3 ≤ ((n : ℝ) + 2) ^ 3 := pow_le_pow_left₀ hn0 (by linarith) 3
    have hl2sq : (1:ℝ) / 8 ≤ Real.log 2 ^ 2 := by nlinarith
    have hl0 : 0 < Real.log 2 := by linarith
    have e : (2:ℝ) ^ 30 * (((n : ℝ) + 2) * Real.log 2) ^ 3 =
        2 ^ 30 * ((n : ℝ) + 2) ^ 3 * Real.log 2 ^ 2 * Real.log 2 := by ring
    rw [e]
    have hm := mul_le_mul hc hl2sq (by norm_num) (by positivity)
    have hm2 := mul_le_mul_of_nonneg_left hm (by positivity : (0:ℝ) ≤ 2 ^ 30)
    have h1 : (2:ℝ) ^ 27 * (n:ℝ) ^ 3 ≤ 2 ^ 30 * ((n : ℝ) + 2) ^ 3 * Real.log 2 ^ 2 := by
      calc (2:ℝ) ^ 27 * (n:ℝ) ^ 3 = 2 ^ 30 * ((n:ℝ) ^ 3 * (1 / 8)) := by ring
        _ ≤ 2 ^ 30 * (((n:ℝ) + 2) ^ 3 * Real.log 2 ^ 2) := hm2
        _ = _ := by ring
    have h1' : (2:ℝ) ^ 27 * (n:ℝ) ^ 3 * Real.log 2 ≤ 2 ^ 30 * ((n : ℝ) + 2) ^ 3 * Real.log 2 ^ 2 * Real.log 2 :=
      mul_le_mul_of_nonneg_right h1 hl0.le
    calc _ = (2:ℝ) ^ 27 * (n:ℝ) ^ 3 * Real.log 2 := by ring
      _ ≤ _ := h1'
