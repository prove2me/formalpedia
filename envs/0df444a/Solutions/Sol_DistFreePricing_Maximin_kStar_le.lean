-- Prove2me | solution 1 for DistFreePricing.Maximin.kStar_le
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:26:53.482207+00:00
-- url     : https://prove2.me/submissions/52f5ce0a-9814-410c-b353-26129d3dceb9

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

theorem solution (c μ σ : ℝ) (hc : 0 ≤ c) (hcμ : c ≤ μ) (hσ : 0 < σ) :
    kStar (tau c μ σ) ≤ 2 * tau c μ σ / 3 ∧ 2 * tau c μ σ / 3 ≤ tau c μ σ ∧
      c ≤ pStar c μ σ := by
  have ht : 0 ≤ tau c μ σ := div_nonneg (by linarith) hσ.le
  obtain ⟨hcub, hnn⟩ := dfp_kStar_cubic_nonneg (tau c μ σ)
  have hk0 := hnn ht
  have hkle : kStar (tau c μ σ) ≤ 2 * tau c μ σ / 3 := by nlinarith [pow_nonneg hk0 3]
  refine ⟨hkle, by linarith, ?_⟩
  have htσ : tau c μ σ * σ = μ - c := by unfold tau; field_simp
  unfold pStar
  have : kStar (tau c μ σ) * σ ≤ tau c μ σ * σ :=
    mul_le_mul_of_nonneg_right (by linarith) hσ.le
  linarith
