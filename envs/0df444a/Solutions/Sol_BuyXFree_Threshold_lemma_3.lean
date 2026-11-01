-- Prove2me | solution 1 for BuyXFree.Threshold.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T16:19:31.856005+00:00
-- url     : https://prove2.me/submissions/aab0a2c9-baf1-4201-95c2-e8ead6c5e433

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

namespace BuyXFree.Threshold.L3Aux
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

/-- `A(1 − A^X) ≥ X A^X (1 − A)` for `0 ≤ A`, `X ≥ 1`. -/
lemma hG (a : ℝ) (ha : 0 ≤ a) (X : ℕ) (hX : 1 ≤ X) :
    (X : ℝ) * a ^ X * (1 - a) ≤ a * (1 - a ^ X) := by
  obtain ⟨n, rfl⟩ : ∃ n, X = n + 1 := ⟨X - 1, by omega⟩
  have := g_nonneg a ha n
  have e : a * (1 - a ^ (n + 1)) - ((n + 1 : ℕ) : ℝ) * a ^ (n + 1) * (1 - a) =
      a * (1 - (n + 1) * a ^ n + n * a ^ (n + 1)) := by push_cast; ring
  nlinarith [mul_nonneg ha this]

end BuyXFree.Threshold.L3Aux

open BuyXFree.Threshold BuyXFree.Threshold.L3Aux in
theorem solution (P : Params) (hP : P.Standing) (hk : P.k = 0)
    (hcond : P.q ≤ A P ∨ (A P < P.q ∧ P.v - P.vbar ≤ A P * P.v))
    (X : ℕ) (hX : 1 ≤ X) (p : ℝ)
    (hlo : pD P X (X - 1) < p) (hhi : p ≤ min (pB P X X) (pD P X X)) :
    P.lam * P.q * X / ((X : ℝ) + P.q) * p ≤ noProgramProfit P := by
  obtain ⟨hl0, hl1, hq0, hq1, hd0, hd1, hvb0, hvbv, hk0⟩ := hP
  have hR0 : 0 ≤ noProgramProfit P :=
    (mul_nonneg hl0 (sub_nonneg.2 hvbv)).trans (le_max_right _ _)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  rcases hl0.lt_or_eq with hlam | hlam
  swap
  · rw [← hlam]; simpa using hR0
  rcases hq0.lt_or_eq with hq | hq
  swap
  · rw [← hq]; simpa using hR0
  have hden1 : 0 < 1 - P.δ + P.lam * P.δ := by nlinarith
  have hden : 0 < 1 - P.δ + P.lam * P.q * P.δ := by nlinarith [mul_pos hlam hq]
  have hA0 : 0 < A P := by unfold A; positivity
  have hA1 : A P < 1 := by unfold A; rw [div_lt_one hden]; linarith
  have hB0 : 0 < A1 P := by unfold A1; positivity
  have hrel : A P * (1 - A1 P) = P.q * A1 P * (1 - A P) := by
    unfold A A1
    field_simp
    ring
  have hpow : A P ^ X < 1 := pow_lt_one₀ hA0.le hA1 (by omega)
  have hpd : 0 < 1 - A P ^ X := by linarith
  -- the price bound p ≤ p^D(X), cleared of denominators
  have hp : p * (A P * (1 - A P ^ X)) ≤ (1 - A P ^ (X + 1)) * (P.v - P.vbar) := by
    have h1 := hhi.trans (min_le_right _ _)
    unfold pD at h1
    simp only [Nat.sub_self, pow_zero, zero_add, pow_one, hk, mul_zero, add_zero, sub_self]
      at h1
    have hD : 0 < P.q * (1 - A P ^ X) * A1 P := by positivity
    rw [le_div_iff₀ hD] at h1
    -- multiply by A
    have h2 : p * (P.q * (1 - A P ^ X) * A1 P) * A P ≤
        (1 - A1 P + P.q * (1 - A P ^ X) * A1 P) * (P.v - P.vbar) * A P :=
      mul_le_mul_of_nonneg_right h1 hA0.le
    have e : (1 - A1 P + P.q * (1 - A P ^ X) * A1 P) * (P.v - P.vbar) * A P =
        P.q * A1 P * ((1 - A P ^ (X + 1)) * (P.v - P.vbar)) := by
      rw [pow_succ]
      linear_combination (P.v - P.vbar) * hrel
    rw [e] at h2
    have h3 : P.q * A1 P * (p * (A P * (1 - A P ^ X))) ≤
        P.q * A1 P * ((1 - A P ^ (X + 1)) * (P.v - P.vbar)) := by
      linarith [h2]
    exact le_of_mul_le_mul_left h3 (by positivity)
  have hG' := hG (A P) hA0.le X hX
  have hR1 : P.lam * (P.v - P.vbar) ≤ noProgramProfit P := le_max_right _ _
  have hR2 : P.lam * P.q * P.v ≤ noProgramProfit P := le_max_left _ _
  have hv0 : 0 ≤ P.v := hvb0.trans hvbv
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  rw [pow_succ] at hp
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  generalize A P = a at *
  generalize a ^ X = c at *
  generalize noProgramProfit P = R at *
  -- now a, c are reals with 0 < a < 1, 0 ≤ c < 1
  have hca : c * a ≤ 1 := by nlinarith
  have hcore : (X : ℝ) * (1 - c * a) ≤ ((X : ℝ) + a) * (1 - c) := by nlinarith
  have hlqX : 0 ≤ P.lam * P.q * X := by positivity
  have hpos : 0 < a * (1 - c) := by positivity
  have step1 : P.lam * P.q * X * (p * (a * (1 - c))) ≤
      P.lam * P.q * X * ((1 - c * a) * (P.v - P.vbar)) :=
    mul_le_mul_of_nonneg_left hp hlqX
  suffices h : P.lam * P.q * X * p * (a * (1 - c)) ≤ R * ((X : ℝ) + P.q) * (a * (1 - c)) from
    le_of_mul_le_mul_right h hpos
  rcases hcond with hqa | ⟨hqa, hvv⟩
  · have hcoef : a * (1 - c) ≤ (X : ℝ) * (1 - c * a) := by
      have h1 : 0 ≤ ((X : ℝ) - 1) * (1 - c * a) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hF : (X : ℝ) * P.q * (1 - c * a) ≤ ((X : ℝ) + P.q) * (a * (1 - c)) := by
      have e1 := mul_le_mul_of_nonneg_left hcore hpos.le
      have e2 := mul_nonneg (sub_nonneg.2 hqa) (sub_nonneg.2 hcoef)
      have e3 := mul_le_mul_of_nonneg_left hcore hA0.le
      nlinarith
    have hvv0 : 0 ≤ P.lam * (P.v - P.vbar) := mul_nonneg hl0 (sub_nonneg.2 hvbv)
    have h4 : P.lam * P.q * X * ((1 - c * a) * (P.v - P.vbar)) ≤
        P.lam * (P.v - P.vbar) * (((X : ℝ) + P.q) * (a * (1 - c))) := by
      have := mul_le_mul_of_nonneg_left hF hvv0
      calc _ = P.lam * (P.v - P.vbar) * ((X : ℝ) * P.q * (1 - c * a)) := by ring
        _ ≤ _ := this
    have h5 : P.lam * (P.v - P.vbar) * (((X : ℝ) + P.q) * (a * (1 - c))) ≤
        R * (((X : ℝ) + P.q) * (a * (1 - c))) :=
      mul_le_mul_of_nonneg_right hR1 (by positivity)
    calc _ = P.lam * P.q * X * (p * (a * (1 - c))) := by ring
      _ ≤ _ := step1
      _ ≤ _ := h4
      _ ≤ _ := h5
      _ = _ := by ring
  · have hpow1 : 0 ≤ 1 - c * a := by linarith
    have h4 : P.lam * P.q * X * ((1 - c * a) * (P.v - P.vbar)) ≤
        P.lam * P.q * X * ((1 - c * a) * (a * P.v)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvv hpow1) hlqX
    have hcore' : (X : ℝ) * (1 - c * a) ≤ ((X : ℝ) + P.q) * (1 - c) := by
      have : 0 ≤ (P.q - a) * (1 - c) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    have h5 : P.lam * P.q * X * ((1 - c * a) * (a * P.v)) ≤
        P.lam * P.q * P.v * (((X : ℝ) + P.q) * (a * (1 - c))) := by
      have := mul_le_mul_of_nonneg_left hcore' (show 0 ≤ P.lam * P.q * P.v * a by positivity)
      calc _ = P.lam * P.q * P.v * a * ((X : ℝ) * (1 - c * a)) := by ring
        _ ≤ _ := this
        _ = _ := by ring
    have h6 : P.lam * P.q * P.v * (((X : ℝ) + P.q) * (a * (1 - c))) ≤
        R * (((X : ℝ) + P.q) * (a * (1 - c))) :=
      mul_le_mul_of_nonneg_right hR2 (by positivity)
    calc _ = P.lam * P.q * X * (p * (a * (1 - c))) := by ring
      _ ≤ _ := step1
      _ ≤ _ := h4
      _ ≤ _ := h5
      _ ≤ _ := h6
      _ = _ := by ring
