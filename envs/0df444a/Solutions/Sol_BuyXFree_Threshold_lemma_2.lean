-- Prove2me | solution 1 for BuyXFree.Threshold.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T16:23:06.057849+00:00
-- url     : https://prove2.me/submissions/f0170390-79cc-4d81-97ae-aada8f4327c3

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

namespace BuyXFree.Threshold.L2Aux
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

end BuyXFree.Threshold.L2Aux

open BuyXFree.Threshold BuyXFree.Threshold.L2Aux in
theorem solution (P : Params) (hP : P.Standing) (hk : P.k = 0)
    (hcond : P.q ≤ 1 / 2 ∨ (1 / 2 < P.q ∧ P.v - P.vbar ≤ P.v / (1 + A1 P)))
    (X τ : ℕ) (hτ1 : 1 ≤ τ) (hτX : τ + 1 ≤ X) (p : ℝ)
    (hlo : pD P X (τ - 1) < p) (hhi : p ≤ min (pB P X τ) (pD P X τ)) :
    P.lam * P.q * X / ((τ : ℝ) + P.q * ((X : ℝ) - τ + 1)) * p ≤ noProgramProfit P := by
  obtain ⟨hl0, hl1, hq0, hq1, hd0, hd1, hvb0, hvbv, hk0⟩ := hP
  obtain ⟨i, rfl⟩ : ∃ i, X = τ + i := ⟨X - τ, by omega⟩
  have hi : 1 ≤ i := by omega
  have hden1 : 0 < 1 - P.δ + P.lam * P.δ := by nlinarith
  have hden : 0 < 1 - P.δ + P.lam * P.q * P.δ := by
    have : 0 ≤ P.lam * P.q * P.δ := by positivity
    linarith
  have hb0 : 0 ≤ A1 P := by unfold A1; positivity
  have hb1 : A1 P < 1 := by unfold A1; rw [div_lt_one hden1]; linarith
  have ha0 : 0 ≤ A P := by unfold A; positivity
  have ha1 : A P < 1 := by unfold A; rw [div_lt_one hden]; linarith
  have hR1 : P.lam * (P.v - P.vbar) ≤ noProgramProfit P := le_max_right _ _
  have hR2 : P.lam * P.q * P.v ≤ noProgramProfit P := le_max_left _ _
  have hv0 : 0 ≤ P.v := hvb0.trans hvbv
  have hvv : 0 ≤ P.v - P.vbar := sub_nonneg.2 hvbv
  have hcondb : P.q ≤ 1 / 2 ∨ (1 + A1 P) * (P.v - P.vbar) ≤ P.v := by
    rcases hcond with h | ⟨_, h⟩
    · exact Or.inl h
    · right
      rw [le_div_iff₀ (by linarith)] at h
      linarith
  -- the price bound p ≤ p^D(τ)
  have hp := hhi.trans (min_le_right _ _)
  unfold pD at hp
  have e1 : τ + i - τ + 1 = i + 1 := by omega
  have e2 : τ + i - τ = i := by omega
  rw [e1, e2, hk, mul_zero, add_zero] at hp
  have hg := g_nonneg (A1 P) hb0 i
  have hpowa : A P ^ τ ≤ 1 := pow_le_one₀ ha0 ha1.le
  have hs0 : 0 ≤ P.q * (1 - A P ^ τ) := mul_nonneg hq0 (by linarith)
  have hcb : A1 P ^ i ≤ A1 P := by
    calc A1 P ^ i ≤ A1 P ^ 1 := pow_le_pow_of_le_one hb0 hb1.le hi
      _ = A1 P := pow_one _
  have hc0 : 0 ≤ A1 P ^ i := pow_nonneg hb0 i
  have hXcast : ((τ + i : ℕ) : ℝ) = (τ : ℝ) + i := by push_cast; ring
  rw [hXcast, show (τ : ℝ) + P.q * ((τ : ℝ) + i - τ + 1) = τ + P.q * (i + 1) by ring]
  rw [pow_succ] at hp hg
  generalize A1 P = b at *
  generalize A1' : b ^ i = c at *
  generalize P.q * (1 - A P ^ τ) = s at *
  generalize noProgramProfit P = R at *
  have hτr : (1 : ℝ) ≤ τ := by exact_mod_cast hτ1
  have hir : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hDn : 0 < 1 - c + s * (c * b) := by
    have : 0 ≤ s * (c * b) := by positivity
    linarith
  rw [le_div_iff₀ hDn] at hp
  have hD : 0 < (τ : ℝ) + P.q * (i + 1) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hD]
  have hlqX : 0 ≤ P.lam * P.q * ((τ : ℝ) + i) := by positivity
  have step1 : P.lam * P.q * ((τ : ℝ) + i) * (p * (1 - c + s * (c * b))) ≤
      P.lam * P.q * ((τ : ℝ) + i) * ((1 - c * b + s * (c * b)) * (P.v - P.vbar)) :=
    mul_le_mul_of_nonneg_left hp hlqX
  suffices h : P.lam * P.q * ((τ : ℝ) + i) * p * (1 - c + s * (c * b)) ≤
      R * ((τ : ℝ) + P.q * (i + 1)) * (1 - c + s * (c * b)) from
    le_of_mul_le_mul_right h hDn
  have hN : 1 - c * b + s * (c * b) = (1 - c + s * (c * b)) + c * (1 - b) := by ring
  have hscb : 0 ≤ s * (c * b) := by positivity
  by_cases hcase : P.q ≤ (1 - P.q) * i
  · -- Case A: bound by λ(v - v̄)
    have hg' : (i : ℝ) * c * (1 - b) ≤ 1 - c := by linarith
    have hc1 : 0 ≤ c * (1 - b) := mul_nonneg hc0 (by linarith)
    have a1 : P.q * (c * (1 - b)) ≤ (1 - P.q) * i * (c * (1 - b)) :=
      mul_le_mul_of_nonneg_right hcase hc1
    have a2 : (1 - P.q) * ((i : ℝ) * c * (1 - b)) ≤ (1 - P.q) * (1 - c) :=
      mul_le_mul_of_nonneg_left hg' (by linarith)
    have a5 : 0 ≤ (1 - P.q) * (1 - c) - P.q * (c * (1 - b)) := by
      have : (1 - P.q) * i * (c * (1 - b)) = (1 - P.q) * ((i : ℝ) * c * (1 - b)) := by ring
      linarith
    have a6 : 0 ≤ (1 - c) - (i : ℝ) * c * (1 - b) := by linarith
    have hK : 0 ≤ ((τ : ℝ) * (1 - P.q) + P.q) * (1 - c) - P.q * ((τ : ℝ) + i) * (c * (1 - b)) := by
      have e : ((τ : ℝ) * (1 - P.q) + P.q) * (1 - c) - P.q * ((τ : ℝ) + i) * (c * (1 - b)) =
          τ * ((1 - P.q) * (1 - c) - P.q * (c * (1 - b))) +
            P.q * ((1 - c) - (i : ℝ) * c * (1 - b)) := by ring
      rw [e]; positivity
    have hq1' : 0 ≤ (τ : ℝ) * (1 - P.q) + P.q := by nlinarith
    have h2 : P.q * ((τ : ℝ) + i) * (1 - c * b + s * (c * b)) ≤
        ((τ : ℝ) + P.q * (i + 1)) * (1 - c + s * (c * b)) := by
      have e : ((τ : ℝ) + P.q * (i + 1)) * (1 - c + s * (c * b)) -
          P.q * ((τ : ℝ) + i) * (1 - c * b + s * (c * b)) =
          (((τ : ℝ) * (1 - P.q) + P.q) * (1 - c) - P.q * ((τ : ℝ) + i) * (c * (1 - b))) +
            ((τ : ℝ) * (1 - P.q) + P.q) * (s * (c * b)) := by ring
      have : 0 ≤ ((τ : ℝ) * (1 - P.q) + P.q) * (s * (c * b)) := mul_nonneg hq1' hscb
      linarith
    have hvv0 : 0 ≤ P.lam * (P.v - P.vbar) := mul_nonneg hl0 hvv
    have h3 := mul_le_mul_of_nonneg_left h2 hvv0
    have h4 : P.lam * (P.v - P.vbar) * (((τ : ℝ) + P.q * (i + 1)) * (1 - c + s * (c * b))) ≤
        R * (((τ : ℝ) + P.q * (i + 1)) * (1 - c + s * (c * b))) :=
      mul_le_mul_of_nonneg_right hR1 (by positivity)
    calc _ = P.lam * P.q * ((τ : ℝ) + i) * (p * (1 - c + s * (c * b))) := by ring
      _ ≤ _ := step1
      _ = P.lam * (P.v - P.vbar) * (P.q * ((τ : ℝ) + i) * (1 - c * b + s * (c * b))) := by ring
      _ ≤ _ := h3
      _ ≤ _ := h4
      _ = _ := by ring
  · -- Case B: (1 - q) i < q, bound by λq(1 + A₁)(v - v̄) ≤ λqv
    push Not at hcase
    have hvb : (1 + b) * (P.v - P.vbar) ≤ P.v := by
      rcases hcondb with h | h
      · exfalso
        have : (1 - P.q) * 1 ≤ (1 - P.q) * i := mul_le_mul_of_nonneg_left hir (by linarith)
        linarith
      · exact h
    have h1 : (τ : ℝ) + i ≤ (τ : ℝ) + P.q * (i + 1) := by
      have : (1 - P.q) * i = i - P.q * i := by ring
      have : P.q * (i + 1) = P.q * i + P.q := by ring
      linarith
    have h2 : 1 - c * b + s * (c * b) ≤ (1 + b) * (1 - c + s * (c * b)) := by
      have e : (1 + b) * (1 - c + s * (c * b)) - (1 - c * b + s * (c * b)) =
          (b - c) + b * (s * (c * b)) := by ring
      have : 0 ≤ b * (s * (c * b)) := mul_nonneg hb0 hscb
      linarith
    have hNpos : 0 ≤ 1 - c * b + s * (c * b) := by
      have : c * b ≤ c := mul_le_of_le_one_right hc0 hb1.le
      linarith
    have h3 : ((τ : ℝ) + i) * (1 - c * b + s * (c * b)) ≤
        ((τ : ℝ) + P.q * (i + 1)) * ((1 + b) * (1 - c + s * (c * b))) :=
      mul_le_mul h1 h2 hNpos hD.le
    have hlq : 0 ≤ P.lam * P.q * (P.v - P.vbar) := by positivity
    have h4 := mul_le_mul_of_nonneg_left h3 hlq
    have h5 : P.lam * P.q * ((τ : ℝ) + P.q * (i + 1)) * (1 - c + s * (c * b)) *
        ((1 + b) * (P.v - P.vbar)) ≤
        P.lam * P.q * ((τ : ℝ) + P.q * (i + 1)) * (1 - c + s * (c * b)) * P.v :=
      mul_le_mul_of_nonneg_left hvb (by positivity)
    have h6 : P.lam * P.q * P.v * (((τ : ℝ) + P.q * (i + 1)) * (1 - c + s * (c * b))) ≤
        R * (((τ : ℝ) + P.q * (i + 1)) * (1 - c + s * (c * b))) :=
      mul_le_mul_of_nonneg_right hR2 (by positivity)
    calc _ = P.lam * P.q * ((τ : ℝ) + i) * (p * (1 - c + s * (c * b))) := by ring
      _ ≤ _ := step1
      _ = P.lam * P.q * (P.v - P.vbar) * (((τ : ℝ) + i) * (1 - c * b + s * (c * b))) := by ring
      _ ≤ _ := h4
      _ = P.lam * P.q * ((τ : ℝ) + P.q * (i + 1)) * (1 - c + s * (c * b)) *
          ((1 + b) * (P.v - P.vbar)) := by ring
      _ ≤ _ := h5
      _ = P.lam * P.q * P.v * (((τ : ℝ) + P.q * (i + 1)) * (1 - c + s * (c * b))) := by ring
      _ ≤ _ := h6
      _ = _ := by ring
