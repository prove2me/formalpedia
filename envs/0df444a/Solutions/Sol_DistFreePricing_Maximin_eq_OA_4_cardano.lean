-- Prove2me | solution 1 for DistFreePricing.Maximin.eq_OA_4_cardano
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:29:27.952824+00:00
-- url     : https://prove2.me/submissions/e6048560-8ee1-4994-bb33-b9270b02f704

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

lemma dfp_phi_hasDerivAt (t k : ℝ) :
    HasDerivAt (phi t) ((-(1 / t)) * (1 - 1 / (1 + k ^ 2)) +
      (1 - k / t) * (2 * k / (1 + k ^ 2) ^ 2)) k := by
  have h1 : (1 + k ^ 2) ≠ 0 := by positivity
  have hA : HasDerivAt (fun x : ℝ => 1 - x / t) (-(1 / t)) k := by
    have := ((hasDerivAt_id k).div_const t).const_sub 1
    simpa using this
  have hB0 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * k) k := by
    have := ((hasDerivAt_pow 2 k).const_add 1)
    simpa using this
  have hB : HasDerivAt (fun x : ℝ => 1 - 1 / (1 + x ^ 2)) (2 * k / (1 + k ^ 2) ^ 2) k := by
    have := (hB0.inv h1).const_sub 1
    have hf : (fun x : ℝ => 1 - 1 / (1 + x ^ 2)) = (fun x => 1 - (fun x : ℝ => 1 + x ^ 2)⁻¹ x) := by
      funext x; simp [one_div]
    rw [hf]
    exact this.congr_deriv (by ring)
  have := hA.mul hB
  exact this

theorem solution (t : ℝ) (ht : 0 ≤ t) :
    (0 < t → ∀ k : ℝ, k ≠ 0 → (deriv (phi t) k = 0 ↔ k ^ 3 + 3 * k = 2 * t)) ∧
    (0 < t → ∀ k : ℝ, 0 ≤ k → k ≤ t → phi t 0 ≤ phi t k ∧ phi t t ≤ phi t k) ∧
    kStar t ^ 3 + 3 * kStar t = 2 * t ∧
    (∀ k : ℝ, k ^ 3 + 3 * k = 2 * t → k = kStar t) ∧
    0 ≤ kStar t := by
  obtain ⟨hcub, hnn⟩ := dfp_kStar_cubic_nonneg t
  refine ⟨?_, ?_, hcub, ?_, hnn ht⟩
  · intro htp k hk
    rw [(dfp_phi_hasDerivAt t k).deriv]
    have h1 : (1 + k ^ 2) ≠ 0 := by positivity
    have e : (-(1 / t)) * (1 - 1 / (1 + k ^ 2)) + (1 - k / t) * (2 * k / (1 + k ^ 2) ^ 2)
        = k * (2 * t - 3 * k - k ^ 3) / (t * (1 + k ^ 2) ^ 2) := by
      field_simp; ring
    rw [e, div_eq_zero_iff, mul_eq_zero]
    constructor
    · rintro ((h | h) | h)
      · exact absurd h hk
      · linarith
      · exfalso; have : t * (1 + k ^ 2) ^ 2 ≠ 0 := by positivity
        exact this h
    · intro h; left; right; linarith
  · intro htp k hk0 hkt
    have hnk : 0 ≤ phi t k := by
      unfold phi
      apply mul_nonneg
      · rw [sub_nonneg, div_le_one htp]; exact hkt
      · rw [sub_nonneg]
        apply div_le_one_of_le₀ (by nlinarith) (by positivity)
    have h0 : phi t 0 = 0 := by unfold phi; simp
    have htt : phi t t = 0 := by unfold phi; rw [div_self htp.ne']; simp
    rw [h0, htt]; exact ⟨hnk, hnk⟩
  · intro k hk
    have : (k - kStar t) * (k ^ 2 + k * kStar t + kStar t ^ 2 + 3) = 0 := by
      linear_combination hk - hcub
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · nlinarith [sq_nonneg (k + kStar t), sq_nonneg k, sq_nonneg (kStar t)]
