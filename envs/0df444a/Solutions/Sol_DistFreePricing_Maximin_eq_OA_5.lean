-- Prove2me | solution 1 for DistFreePricing.Maximin.eq_OA_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:28:06.723242+00:00
-- url     : https://prove2.me/submissions/1597641a-a460-4d0a-8eb8-304e43c41d27

import Mathlib
import Definitions.Def_DistFreePricing_Maximin_Setting

open DistFreePricing.Maximin

lemma dfp_kStar_cubic_nonneg (t : ℝ) :
    kStar t ^ 3 + 3 * kStar t = 2 * t ∧ (0 ≤ t → 0 ≤ kStar t) := by
  set s := Real.sqrt (t ^ 2 + 1) with hs
  have hs2 : s ^ 2 = t ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hst : |t| < s := by
    rw [hs]; rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have h1 : 0 < s + t := by have := neg_abs_le t; linarith
  have h2 : 0 < s - t := by have := le_abs_self t; linarith
  set a := (s + t) ^ ((1 : ℝ) / 3) with ha
  set b := (s - t) ^ ((1 : ℝ) / 3) with hb
  have ha3 : a ^ 3 = s + t := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul h1.le]; norm_num
  have hb3 : b ^ 3 = s - t := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul h2.le]; norm_num
  have hab : a * b = 1 := by
    rw [ha, hb, ← Real.mul_rpow h1.le h2.le]
    have : (s + t) * (s - t) = 1 := by nlinarith
    rw [this, Real.one_rpow]
  have hk : kStar t = a - b := rfl
  refine ⟨?_, ?_⟩
  · rw [hk]
    have : (a - b) ^ 3 + 3 * (a - b) = a ^ 3 - b ^ 3 - 3 * (a * b) * (a - b) + 3 * (a - b) := by ring
    rw [this, ha3, hb3, hab]; ring
  · intro ht
    rw [hk, sub_nonneg, ha, hb]
    exact Real.rpow_le_rpow h2.le (by linarith) (by norm_num)

theorem solution (t : ℝ) (ht : 0 < t) :
    (∀ k : ℝ, 0 ≤ k → k ≤ t → phi t k ≤ phi t (kStar t)) ∧
    phi t (kStar t) = kStar t ^ 2 / (kStar t ^ 2 + 3) ∧
    phi t (kStar t) = kStar t ^ 3 / (2 * t) ∧
    phi t (kStar t) = 1 - 3 / (2 * t) * kStar t := by
  obtain ⟨hcub, hnn⟩ := dfp_kStar_cubic_nonneg t
  have hK0 := hnn ht.le
  set K := kStar t with hK
  have hval : phi t K = 1 - 3 / (2 * t) * K := by
    unfold phi
    have h1 : (1 + K ^ 2) ≠ 0 := by positivity
    field_simp
    linear_combination (1 : ℝ) * hcub
  refine ⟨?_, ?_, ?_, hval⟩
  · intro k hk0 _
    rw [hval]
    unfold phi
    have h1 : (0 : ℝ) < 1 + k ^ 2 := by positivity
    have key : 2 * (t - k) * k ^ 2 ≤ (2 * t - 3 * K) * (1 + k ^ 2) := by
      nlinarith [mul_nonneg (sq_nonneg (k - K)) (by linarith : (0:ℝ) ≤ 2 * k + K)]
    have e1 : (1 - k / t) * (1 - 1 / (1 + k ^ 2)) = 2 * (t - k) * k ^ 2 / (2 * t * (1 + k ^ 2)) := by
      field_simp
      ring
    have e2 : 1 - 3 / (2 * t) * K = (2 * t - 3 * K) * (1 + k ^ 2) / (2 * t * (1 + k ^ 2)) := by
      field_simp
    rw [e1, e2]
    exact div_le_div_of_nonneg_right key (by positivity)
  · rw [hval]
    have h3 : K ^ 2 + 3 ≠ 0 := by positivity
    field_simp
    linear_combination (-3 : ℝ) * hcub
  · rw [hval]
    field_simp
    linear_combination (-1 : ℝ) * hcub
