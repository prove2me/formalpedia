-- Prove2me | solution 1 for BuyXFree.Threshold.converse_c
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T16:39:15.882313+00:00
-- url     : https://prove2.me/submissions/2ad92524-e42f-4cd4-98db-9e71fe909a07

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

/-- A state where she buys only against the low outside option. -/
lemma eq_low (P : Params) (hP : P.Standing) (B Jx : ℝ)
    (h : Jx = P.lam * P.q * B + P.lam * (1 - P.q) * (P.vbar + P.δ * Jx)
      + (1 - P.lam) * P.δ * Jx) :
    P.δ * Jx = A P * B + P.lam * (1 - P.q) * P.δ * P.vbar / (1 - P.δ + P.lam * P.q * P.δ) := by
  obtain ⟨hl0, hl1, hq0, hq1, hd0, hd1, -⟩ := hP
  have hden : 0 < 1 - P.δ + P.lam * P.q * P.δ := by
    have : 0 ≤ P.lam * P.q * P.δ := by positivity
    linarith
  have key : P.δ * Jx * (1 - P.δ + P.lam * P.q * P.δ) =
      P.lam * P.q * P.δ * B + P.lam * (1 - P.q) * P.δ * P.vbar := by
    linear_combination P.δ * h
  unfold A
  rw [div_mul_eq_mul_div, ← add_div, eq_div_iff hden.ne']
  linear_combination key

lemma hrel (P : Params) (hP : P.Standing) :
    A P * (1 - A1 P) = P.q * A1 P * (1 - A P) := by
  obtain ⟨hl0, hl1, hq0, hq1, hd0, hd1, -⟩ := hP
  have hden1 : 0 < 1 - P.δ + P.lam * P.δ := by nlinarith
  have hden : 0 < 1 - P.δ + P.lam * P.q * P.δ := by
    have : 0 ≤ P.lam * P.q * P.δ := by positivity
    linarith
  unfold A A1
  field_simp
  ring

end BuyXFree.Threshold.CvAux

open BuyXFree.Threshold BuyXFree.Threshold.CvAux in
theorem solution (P : Params) (hP : P.Standing) (hlam : 0 < P.lam) (hq : 0 < P.q)
    (p : ℝ) (X : ℕ) (hX : 1 ≤ X) (J : ℕ → ℝ) (hJ : IsValueFn P p X J)
    (h28 : BuysLow P p J 0) (h29 : ¬ BuysHigh P p J (X - 1)) (h30 : RedeemsHigh P X J) :
    p ≤ pB P X X ∧ pD P X (X - 1) < p ∧ p ≤ pD P X X := by
  have hP' := hP
  obtain ⟨hl0, hl1, hq0, hq1, hd0, hd1, hvb0, hvbv, hk0⟩ := hP'
  have hBL : ∀ x < X, BuysLow P p J x := by
    intro x hx
    induction x with
    | zero => exact h28
    | succ n ih => exact (corollary_1 P hP p X hX J hJ n (by omega)).1 (ih (by omega))
  have hRL : RedeemsLow P X J := by
    have := lemma_4 P hP p X hX J hJ; unfold RedeemsLow; linarith
  have hnBH : ∀ x < X, ¬ BuysHigh P p J x := by
    intro x hx hb
    apply h29
    have : ∀ n, x + n < X → BuysHigh P p J (x + n) := by
      intro n
      induction n with
      | zero => intro _; exact hb
      | succ n ih =>
        intro hn
        exact (corollary_1 P hP p X hX J hJ (x + n) (by omega)).2 (ih (by omega))
    have := this (X - 1 - x) (by omega)
    rwa [show x + (X - 1 - x) = X - 1 by omega] at this
  set E := P.lam * (1 - P.q) * P.δ * P.vbar / (1 - P.δ + P.lam * P.q * P.δ) with hE
  have hEq : ∀ x < X, P.δ * J x = A P * (P.v - p + P.δ * J (x + 1)) + E := by
    intro x hx
    have h := hJ.1 x hx
    have hb := hnBH x hx
    have hl := hBL x hx
    unfold BuysHigh at hb
    unfold BuysLow at hl
    rw [max_eq_left hl, max_eq_right (le_of_lt (not_le.1 hb))] at h
    exact eq_low P hP _ _ h
  have hEX : P.δ * J X = A1 P * (P.v + P.k + P.δ * J 0) := by
    have h := hJ.2
    have hb := h30
    unfold RedeemsHigh at hb
    rw [max_eq_left (by linarith), max_eq_left hb] at h
    exact eq_both P hP _ _ h
  have hden : 0 < 1 - P.δ + P.lam * P.q * P.δ := by nlinarith [mul_pos hlam hq]
  have hden1 : 0 < 1 - P.δ + P.lam * P.δ := by nlinarith
  have ha0 : 0 < A P := by unfold A; positivity
  have ha1 : A P < 1 := by unfold A; rw [div_lt_one hden]; nlinarith
  have hb0 : 0 < A1 P := by unfold A1; positivity
  have hb1 : A1 P < 1 := by unfold A1; rw [div_lt_one hden1]; nlinarith
  have hR := hrel P hP
  have hqE : E * P.q = A P * (1 - P.q) * P.vbar := by
    rw [hE]; unfold A; ring
  have hR2 : (1 - A1 P) * E = A1 P * (1 - A P) * (1 - P.q) * P.vbar := by
    have h : P.q * ((1 - A1 P) * E - A1 P * (1 - A P) * (1 - P.q) * P.vbar) = 0 := by
      linear_combination (1 - A1 P) * hqE + (1 - P.q) * P.vbar * hR
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h hq.ne'
    · linarith
  set u : ℕ → ℝ := fun x => P.δ * J x with hu
  have hG := geom u (A P) (A P * (P.v - p) + E) 0 X (Nat.zero_le _)
    (fun x _ hx => by simp only [hu]; rw [hEq x hx]; ring)
  have F1 : u 0 = A P * (P.v - p) + E + A P * u 1 := by
    simp only [hu]; rw [hEq 0 (by omega)]; ring
  have Fm : u (X - 1) = A P * (P.v - p) + E + A P * u X := by
    simp only [hu]; rw [hEq (X - 1) (by omega), Nat.sub_add_cancel hX]; ring
  have F3 : u X = A1 P * (P.v + P.k) + A1 P * u 0 := by
    simp only [hu]; rw [hEX]; ring
  have H28 : u 0 ≤ P.v - p + u 1 := h28
  have H29 : P.v - p + u X < P.vbar + u (X - 1) := by
    have := h29; unfold BuysHigh at this; rw [Nat.sub_add_cancel hX] at this
    simp only [hu]; linarith
  have H30 : P.vbar + u X ≤ P.v + P.k + u 0 := h30
  simp only [Nat.sub_zero] at hG
  have hZ : A P ^ X < 1 := pow_lt_one₀ ha0.le ha1 (by omega)
  have hZ0 : 0 ≤ A P ^ X := by positivity
  have hW : A P ^ X = A P ^ (X - 1) * A P := by
    rw [← pow_succ, Nat.sub_add_cancel hX]
  have hW0 : 0 ≤ A P ^ (X - 1) := by positivity
  have hW1 : A P ^ (X - 1) ≤ 1 := pow_le_one₀ ha0.le ha1.le
  unfold pB pD
  simp only [Nat.sub_self, pow_zero, zero_add, pow_one, mul_one, sub_self, one_mul, mul_zero,
    show X - (X - 1) = 1 by omega, one_add_one_eq_two]
  generalize A1 P = b at *
  generalize A P ^ (X - 1) = W at *
  generalize A P = a at *
  generalize a ^ X = Z at *
  generalize u 0 = u0 at *
  generalize u 1 = u1 at *
  generalize u X = uX at *
  generalize u (X - 1) = uXm at *
  have hbZ : 0 < 1 - b * Z := by nlinarith
  have K0 : ((1 - a) * uX - (a * (P.v - p) + E)) * (1 - b * Z) =
      b * (1 - a) * ((P.v + P.k) - P.q * (P.v - p) - (1 - P.q) * P.vbar) := by
    linear_combination (1 - a) * F3 + b * hG - hR2 - (P.v - p) * hR
  refine ⟨?_, ?_, ?_⟩
  · -- (28) ⇒ p ≤ p^B(X)
    have T : 0 ≤ a * (P.v - p + u1 - u0) := mul_nonneg ha0.le (by linarith)
    have e1 : a * (P.v - p) + Z * ((1 - a) * uX - (a * (P.v - p) + E)) =
        a * (P.v - p + u1 - u0) := by linear_combination F1 - hG
    have e2 : a * (P.v - p) * (1 - b * Z) +
        Z * (b * (1 - a) * ((P.v + P.k) - P.q * (P.v - p) - (1 - P.q) * P.vbar)) =
        (1 - b * Z) * (a * (P.v - p + u1 - u0)) := by
      rw [← e1]; linear_combination (-Z) * K0
    have hd : 0 < P.q * (1 - Z) := by
      have : 0 < 1 - Z := by linarith
      positivity
    rw [le_div_iff₀ hd]
    have K3 : a * ((P.q * (1 - Z * b) * P.v + (1 - P.q) * Z * (1 - b) * (P.v - P.vbar) +
        Z * (1 - b) * P.k) - p * (P.q * (1 - Z))) =
        P.q * ((1 - b * Z) * (a * (P.v - p + u1 - u0))) := by
      rw [← e2]
      linear_combination Z * (P.k + p * P.q - P.q * P.v + P.q * P.vbar + P.v - P.vbar) * hR
    have K4 : 0 ≤ a * ((P.q * (1 - Z * b) * P.v + (1 - P.q) * Z * (1 - b) * (P.v - P.vbar) +
        Z * (1 - b) * P.k) - p * (P.q * (1 - Z))) := by
      rw [K3]; exact mul_nonneg hq0 (mul_nonneg hbZ.le T)
    have := (mul_nonneg_iff_of_pos_left ha0).1 K4
    linarith
  · -- (29) ⇒ p^D(X-1) < p
    have e : ((1 - a) * uX - (a * (P.v - p) + E)) - (p - (P.v - P.vbar)) =
        (P.v - p + uX) - (P.vbar + uXm) := by linear_combination Fm
    have K1 : (1 - a) * uX - (a * (P.v - p) + E) < p - (P.v - P.vbar) := by linarith
    have K2 : b * (1 - a) * ((P.v + P.k) - P.q * (P.v - p) - (1 - P.q) * P.vbar) <
        (p - (P.v - P.vbar)) * (1 - b * Z) := by
      rw [← K0]; exact mul_lt_mul_of_pos_right K1 hbZ
    have hd : 0 < 1 - b + P.q * (1 - W) * b ^ 2 := by
      have : 0 ≤ P.q * (1 - W) * b ^ 2 := by
        have : 0 ≤ 1 - W := by linarith
        positivity
      linarith
    rw [div_lt_iff₀ hd]
    have K3 : (1 - a) * (p * (1 - b + P.q * (1 - W) * b ^ 2) -
        ((1 - b ^ 2 + P.q * (1 - W) * b ^ 2) * (P.v - P.vbar) + b * (1 - b) * P.k)) =
        (1 - b) * ((p - (P.v - P.vbar)) * (1 - b * Z) -
          b * (1 - a) * ((P.v + P.k) - P.q * (P.v - p) - (1 - P.q) * P.vbar)) := by
      linear_combination b * (1 - b) * (p - P.v + P.vbar) * hW +
        (W * b - 1) * (p - P.v + P.vbar) * hR
    have K4 : 0 < (1 - a) * (p * (1 - b + P.q * (1 - W) * b ^ 2) -
        ((1 - b ^ 2 + P.q * (1 - W) * b ^ 2) * (P.v - P.vbar) + b * (1 - b) * P.k)) := by
      rw [K3]; exact mul_pos (by linarith) (by linarith)
    have := (mul_pos_iff_of_pos_left (show 0 < 1 - a by linarith)).1 K4
    linarith
  · -- (30) ⇒ p ≤ p^D(X)
    have e : (1 - Z) * ((1 - a) * uX - (a * (P.v - p) + E)) = (1 - a) * (uX - u0) := by
      linear_combination hG
    have K1 : (1 - Z) * ((1 - a) * uX - (a * (P.v - p) + E)) ≤
        (1 - a) * (P.v + P.k - P.vbar) := by
      rw [e]; exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have K2 : (1 - a) * ((1 - Z) * b * ((P.v + P.k) - P.q * (P.v - p) - (1 - P.q) * P.vbar)) ≤
        (1 - a) * ((P.v + P.k - P.vbar) * (1 - b * Z)) := by
      calc (1 - a) * ((1 - Z) * b * ((P.v + P.k) - P.q * (P.v - p) - (1 - P.q) * P.vbar))
          = ((1 - Z) * ((1 - a) * uX - (a * (P.v - p) + E))) * (1 - b * Z) := by
            linear_combination (-(1 - Z)) * K0
        _ ≤ ((1 - a) * (P.v + P.k - P.vbar)) * (1 - b * Z) :=
            mul_le_mul_of_nonneg_right K1 hbZ.le
        _ = _ := by ring
    have K3 := le_of_mul_le_mul_left K2 (by linarith)
    have hd : 0 < P.q * (1 - Z) * b := by
      have : 0 < 1 - Z := by linarith
      positivity
    rw [le_div_iff₀ hd]
    have e30 : ((1 - b + P.q * (1 - Z) * b) * (P.v - P.vbar) + (1 - b) * P.k) -
        p * (P.q * (1 - Z) * b) = (P.v + P.k - P.vbar) * (1 - b * Z) -
        (1 - Z) * b * ((P.v + P.k) - P.q * (P.v - p) - (1 - P.q) * P.vbar) := by ring
    linarith
