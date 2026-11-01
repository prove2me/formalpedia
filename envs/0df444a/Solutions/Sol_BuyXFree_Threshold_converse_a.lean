-- Prove2me | solution 1 for BuyXFree.Threshold.converse_a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T16:28:49.253616+00:00
-- url     : https://prove2.me/submissions/fdbec974-5c91-4211-92ed-cda516420060

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model
import Theorems.Thm_BuyXFree_Threshold_corollary_1
import Theorems.Thm_BuyXFree_Threshold_lemma_4
import Theorems.Thm_BuyXFree_Threshold_lemma_5

namespace BuyXFree.Threshold.CvAux
open BuyXFree.Threshold

/-- Iterating `u x = C + r u(x+1)` on `m ≤ x < n`. -/
lemma geom (u : ℕ → ℝ) (r C : ℝ) (m n : ℕ) (hmn : m ≤ n)
    (h : ∀ x, m ≤ x → x < n → u x = C + r * u (x + 1)) :
    (1 - r) * u m - C = r ^ (n - m) * ((1 - r) * u n - C) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [ih (fun x h1 h2 => h x h1 (by omega)), h n hmn (by omega),
      show n + 1 - m = (n - m) + 1 by omega, pow_succ]
    ring

/-- A state where she buys under both outside options: `δJ(x) = A₁ (B)`. -/
lemma eq_both (P : Params) (hP : P.Standing) (B Jx : ℝ)
    (h : Jx = P.lam * P.q * B + P.lam * (1 - P.q) * B + (1 - P.lam) * P.δ * Jx) :
    P.δ * Jx = A1 P * B := by
  obtain ⟨hl0, hl1, hq0, hq1, hd0, hd1, -⟩ := hP
  have hden : 0 < 1 - P.δ + P.lam * P.δ := by nlinarith
  unfold A1
  rw [div_mul_eq_mul_div, eq_div_iff hden.ne']
  linear_combination (1 - P.δ + P.lam * P.δ) * P.δ * h - P.δ * (1 - P.δ + P.lam * P.δ) * h
    + P.δ * h

end BuyXFree.Threshold.CvAux

open BuyXFree.Threshold BuyXFree.Threshold.CvAux in
theorem solution (P : Params) (hP : P.Standing) (hlam : 0 < P.lam) (hq : 0 < P.q)
    (p : ℝ) (X : ℕ) (hX : 1 ≤ X) (J : ℕ → ℝ) (hJ : IsValueFn P p X J)
    (h24 : BuysHigh P p J 0) :
    p ≤ pD P X 0 := by
  have hP' := hP
  obtain ⟨hl0, hl1, hq0, hq1, hd0, hd1, hvb0, hvbv, hk0⟩ := hP'
  -- behaviour: she buys/redeems everywhere
  have hBH : ∀ x < X, BuysHigh P p J x := by
    intro x hx
    induction x with
    | zero => exact h24
    | succ n ih => exact (corollary_1 P hP p X hX J hJ n (by omega)).2 (ih (by omega))
  have hRH : RedeemsHigh P X J := by
    have h := hBH (X - 1) (by omega)
    unfold BuysHigh at h
    rw [Nat.sub_add_cancel hX] at h
    have := lemma_5 P hP p X hX J hJ (by linarith)
    unfold RedeemsHigh; linarith
  have hEq : ∀ x < X, P.δ * J x = A1 P * (P.v - p + P.δ * J (x + 1)) := by
    intro x hx
    have h := hJ.1 x hx
    have hb := hBH x hx
    unfold BuysHigh at hb
    rw [max_eq_left (by linarith), max_eq_left hb] at h
    exact eq_both P hP _ _ h
  have hEX : P.δ * J X = A1 P * (P.v + P.k + P.δ * J 0) := by
    have h := hJ.2
    have hb := hRH
    unfold RedeemsHigh at hb
    rw [max_eq_left (by linarith), max_eq_left hb] at h
    exact eq_both P hP _ _ h
  -- constants
  have hden1 : 0 < 1 - P.δ + P.lam * P.δ := by nlinarith
  have hb0 : 0 < A1 P := by unfold A1; positivity
  have hb1 : A1 P < 1 := by unfold A1; rw [div_lt_one hden1]; nlinarith
  set u : ℕ → ℝ := fun x => P.δ * J x with hu
  have hG := geom u (A1 P) (A1 P * (P.v - p)) 0 X (Nat.zero_le _)
    (fun x _ hx => by simp only [hu]; rw [hEq x hx]; ring)
  have F1 : u 0 = A1 P * (P.v - p) + A1 P * u 1 := by
    simp only [hu]; rw [hEq 0 (by omega)]; ring
  have F3 : u X = A1 P * (P.v + P.k) + A1 P * u 0 := by
    simp only [hu]; rw [hEX]; ring
  have H : P.vbar + u 0 ≤ P.v - p + u 1 := h24
  simp only [Nat.sub_zero] at hG
  -- unfold the target
  unfold pD
  simp only [pow_zero, sub_self, mul_zero, zero_mul, add_zero, Nat.sub_zero]
  have hZ : A1 P ^ X < 1 := pow_lt_one₀ hb0.le hb1 (by omega)
  rw [le_div_iff₀ (by linarith), pow_succ]
  have hZ0 : 0 ≤ A1 P ^ X := by positivity
  generalize A1 P = b at *
  generalize b ^ X = Z at *
  -- b v̄ ≤ (1 - b) u0
  have K1 : b * P.vbar ≤ (1 - b) * u 0 := by
    have := mul_le_mul_of_nonneg_left H hb0.le
    linarith
  -- (1 - b) u0 (1 - Z b) = b (v - p)(1 - Z) + Z b (1 - b)(v + k)
  have K2 : (1 - b) * u 0 * (1 - Z * b) =
      b * (P.v - p) * (1 - Z) + Z * b * (1 - b) * (P.v + P.k) := by
    linear_combination hG + Z * (1 - b) * F3
  have hZb : 0 ≤ 1 - Z * b := by nlinarith
  have K3 : b * P.vbar * (1 - Z * b) ≤ (1 - b) * u 0 * (1 - Z * b) :=
    mul_le_mul_of_nonneg_right K1 hZb
  rw [K2] at K3
  have K4 : b * (p * (1 - Z)) ≤ b * ((1 - Z * b) * (P.v - P.vbar) + Z * (1 - b) * P.k) := by
    linarith
  exact le_of_mul_le_mul_left K4 hb0
