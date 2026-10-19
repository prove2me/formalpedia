-- Prove2me | solution 1 for BenfordLaw.benford_mean_variance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:58:30.760889+00:00
-- url     : https://prove2.me/submissions/26950266-f2f0-4e91-8294-df6dbf9e74d9

import Mathlib
import Definitions.Def_BenfordLaw_Defs
open BenfordLaw

lemma sum_Icc_one_nine (f : ℕ → ℝ) : ∑ d ∈ Finset.Icc (1 : ℕ) 9, f d =
    f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  rw [show Finset.Icc (1 : ℕ) 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9} by rfl]
  simp [Finset.sum_insert]
  ring

theorem solution :
    |(∑ d ∈ Finset.Icc (1 : ℕ) 9, (d : ℝ) * benfordProb 10 d) - 3.440| < 0.0005 ∧
      |((∑ d ∈ Finset.Icc (1 : ℕ) 9, (d : ℝ) ^ 2 * benfordProb 10 d) -
          (∑ d ∈ Finset.Icc (1 : ℕ) 9, (d : ℝ) * benfordProb 10 d) ^ 2) - 6.057| < 0.0005 := by
  set L2 := Real.log 2
  set L3 := Real.log 3
  set L5 := Real.log 5
  set L7 := Real.log 7
  have h4 : Real.log 4 = 2 * L2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num; rfl
  have h6 : Real.log 6 = L2 + L3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h8 : Real.log 8 = 3 * L2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num; rfl
  have h9 : Real.log 9 = 2 * L3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num; rfl
  have h10 : Real.log 10 = L2 + L5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  -- numerical facts
  have a1 := Real.log_two_gt_d9
  have a2 := Real.log_two_lt_d9
  have s1 := Real.abs_log_sub_add_sum_range_le (x := 1/9) (by norm_num) 10
  have e1 : Real.log (1 - 1/9) = 3 * L2 - 2 * L3 := by
    rw [show (1 : ℝ) - 1/9 = 2^3 / 3^2 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]
    push_cast; ring
  have s2 := Real.abs_log_sub_add_sum_range_le (x := 1/25) (by norm_num) 8
  have e2 : Real.log (1 - 1/25) = 3 * L2 + L3 - 2 * L5 := by
    rw [show (1 : ℝ) - 1/25 = (2^3 * 3) / 5^2 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  have s3 := Real.abs_log_sub_add_sum_range_le (x := 1/50) (by norm_num) 6
  have e3 : Real.log (1 - 1/50) = 2 * L7 - L2 - 2 * L5 := by
    rw [show (1 : ℝ) - 1/50 = 7^2 / (2 * 5^2) by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [e1] at s1
  rw [e2] at s2
  rw [e3] at s3
  norm_num [Finset.sum_range_succ] at s1 s2 s3
  rw [abs_le] at s1 s2 s3
  obtain ⟨s1a, s1b⟩ := s1
  obtain ⟨s2a, s2b⟩ := s2
  obtain ⟨s3a, s3b⟩ := s3
  have hD : 0 < L2 + L5 := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 5)]
  -- closed forms
  set S := 7 * L2 + 4 * L3 + L5 + L7
  set T := 3 * L2 + 5 * L3 + 7 * (2 * L2) + 9 * L5 + 11 * (L2 + L3) + 13 * L7 + 15 * (3 * L2) +
    17 * (2 * L3)
  have hM : ∑ d ∈ Finset.Icc (1 : ℕ) 9, (d : ℝ) * benfordProb 10 d = 9 - S / (L2 + L5) := by
    rw [sum_Icc_one_nine]
    simp only [benfordProb, Real.logb]
    norm_num
    simp only [Real.log_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, h4, h6, h8, h9, h10,
      ]
    field_simp
    ring
  have hE : ∑ d ∈ Finset.Icc (1 : ℕ) 9, (d : ℝ) ^ 2 * benfordProb 10 d = 81 - T / (L2 + L5) := by
    rw [sum_Icc_one_nine]
    simp only [benfordProb, Real.logb]
    norm_num
    simp only [Real.log_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, h4, h6, h8, h9, h10,
      ]
    field_simp
    ring
  have hS1 : 5.559763 < S / (L2 + L5) := by rw [lt_div_iff₀ hD]; linarith
  have hS2 : S / (L2 + L5) < 5.5597631 := by rw [div_lt_iff₀ hD]; linarith
  have hT1 : 63.1082569 < T / (L2 + L5) := by rw [lt_div_iff₀ hD]; linarith
  have hT2 : T / (L2 + L5) < 63.1082571 := by rw [div_lt_iff₀ hD]; linarith
  rw [hE, hM]
  set m := 9 - S / (L2 + L5)
  have hm1 : 3.4402369 < m := by linarith
  have hm2 : m < 3.440237 := by linarith
  constructor
  · rw [abs_lt]; constructor <;> linarith
  · rw [abs_lt]; constructor <;> nlinarith
