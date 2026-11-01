-- Prove2me | solution 1 for BuyXFree.Threshold.case_a_d_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T16:15:35.461608+00:00
-- url     : https://prove2.me/submissions/2b5180d7-f5c2-472f-9c98-3c644e6783f8

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

namespace BuyXFree.Threshold.CADAux
open BuyXFree.Threshold

lemma g_nonneg (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ 1 - (n + 1) * a ^ n + n * a ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : 1 - ((n + 1 : ℕ) + 1) * a ^ (n + 1) + ((n + 1 : ℕ) : ℝ) * a ^ (n + 1 + 1) =
        (1 - (n + 1) * a ^ n + n * a ^ (n + 1)) + (n + 1) * a ^ n * (1 - a) ^ 2 := by
      push_cast; ring
    rw [h]
    have : 0 ≤ (n + 1 : ℝ) * a ^ n * (1 - a) ^ 2 := by positivity
    linarith

/-- For `0 ≤ a < 1` and `n ≥ 1`: `n/(n+1) · (1 − a^{n+1})/(1 − a^n) ≤ 1`. -/
lemma key (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) (hn : 1 ≤ n) (c p : ℝ) (hc : 0 ≤ c)
    (hp : p ≤ (1 - a ^ (n + 1)) * c / (1 - a ^ n)) :
    (n : ℝ) / ((n : ℝ) + 1) * p ≤ c := by
  have hpow : a ^ n < 1 := pow_lt_one₀ ha ha1 (by omega)
  have hd : 0 < 1 - a ^ n := by linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hg := g_nonneg a ha n
  rw [le_div_iff₀ hd] at hp
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  -- n * p ≤ c * (n+1)
  have h1 : (n : ℝ) * (p * (1 - a ^ n)) ≤ n * ((1 - a ^ (n + 1)) * c) :=
    mul_le_mul_of_nonneg_left hp hn'.le
  have h2 : (n : ℝ) * (1 - a ^ (n + 1)) ≤ (n + 1) * (1 - a ^ n) := by
    rw [pow_succ] at hg ⊢; nlinarith
  have h3 : (n : ℝ) * ((1 - a ^ (n + 1)) * c) ≤ (n + 1) * (1 - a ^ n) * c := by
    nlinarith
  -- n p (1 - a^n) ≤ c (n+1) (1 - a^n)
  have h4 : (n * p) * (1 - a ^ n) ≤ (c * (n + 1)) * (1 - a ^ n) := by nlinarith
  exact le_of_mul_le_mul_right h4 hd

end BuyXFree.Threshold.CADAux

open BuyXFree.Threshold BuyXFree.Threshold.CADAux in
theorem solution (P : Params) (hP : P.Standing) (hk : P.k = 0) (X : ℕ) (hX : 1 ≤ X) :
    (∀ p : ℝ, p ≤ pD P X 0 → P.lam * X / ((X : ℝ) + 1) * p ≤ P.lam * (P.v - P.vbar)) ∧
      (∀ p : ℝ, p ≤ pdUpper P X → P.lam * P.q * X / ((X : ℝ) + 1) * p ≤ P.lam * P.q * P.v) := by
  obtain ⟨hl0, hl1, hq0, hq1, hd0, hd1, hvb0, hvbv, hk0⟩ := hP
  have hden1 : 0 < 1 - P.δ + P.lam * P.δ := by nlinarith
  have hden : 0 < 1 - P.δ + P.lam * P.q * P.δ := by
    have : 0 ≤ P.lam * P.q * P.δ := by positivity
    linarith
  have hA1 : 0 ≤ A1 P := by unfold A1; positivity
  have hA11 : A1 P < 1 := by
    unfold A1; rw [div_lt_one hden1]; linarith
  have hA : 0 ≤ A P := by unfold A; positivity
  have hA1' : A P < 1 := by
    unfold A; rw [div_lt_one hden]; linarith
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · have hp' : p ≤ (1 - A1 P ^ (X + 1)) * (P.v - P.vbar) / (1 - A1 P ^ X) := by
      convert hp using 1
      unfold pD
      simp [hk]
    have := key (A1 P) hA1 hA11 X hX (P.v - P.vbar) p (by linarith) hp'
    calc P.lam * X / ((X : ℝ) + 1) * p = P.lam * ((X : ℝ) / ((X : ℝ) + 1) * p) := by ring
      _ ≤ P.lam * (P.v - P.vbar) := mul_le_mul_of_nonneg_left this hl0
  · have hp' : p ≤ (1 - A P ^ (X + 1)) * P.v / (1 - A P ^ X) := by
      convert hp using 1
      unfold pdUpper
      simp [hk]
    have := key (A P) hA hA1' X hX P.v p (by linarith) hp'
    calc P.lam * P.q * X / ((X : ℝ) + 1) * p = P.lam * P.q * ((X : ℝ) / ((X : ℝ) + 1) * p) := by
          ring
      _ ≤ P.lam * P.q * P.v := mul_le_mul_of_nonneg_left this (by positivity)
