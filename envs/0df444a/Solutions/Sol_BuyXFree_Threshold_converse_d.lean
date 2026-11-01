-- Prove2me | solution 1 for BuyXFree.Threshold.converse_d
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T16:30:42.33029+00:00
-- url     : https://prove2.me/submissions/ada1231d-567c-4843-9943-31af63f67f10

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
    (h31 : BuysLow P p J 0) (h32 : ¬ RedeemsHigh P X J) :
    p ≤ pdUpper P X ∧ pD P X X < p := by
  have hP' := hP
  obtain ⟨hl0, hl1, hq0, hq1, hd0, hd1, hvb0, hvbv, hk0⟩ := hP'
  have hBL : ∀ x < X, BuysLow P p J x := by
    intro x hx
    induction x with
    | zero => exact h31
    | succ n ih => exact (corollary_1 P hP p X hX J hJ n (by omega)).1 (ih (by omega))
  have hRL : RedeemsLow P X J := by
    have := lemma_4 P hP p X hX J hJ; unfold RedeemsLow; linarith
  have hnBHX : ¬ BuysHigh P p J (X - 1) := by
    intro h
    unfold BuysHigh at h
    rw [Nat.sub_add_cancel hX] at h
    have := lemma_5 P hP p X hX J hJ (by linarith)
    exact h32 (by unfold RedeemsHigh; linarith)
  have hnBH : ∀ x < X, ¬ BuysHigh P p J x := by
    intro x hx hb
    apply hnBHX
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
  have hEX : P.δ * J X = A P * (P.v + P.k + P.δ * J 0) + E := by
    have h := hJ.2
    have hb := h32
    have hl := hRL
    unfold RedeemsHigh at hb
    unfold RedeemsLow at hl
    rw [max_eq_left hl, max_eq_right (le_of_lt (not_le.1 hb))] at h
    exact eq_low P hP _ _ h
  have hden : 0 < 1 - P.δ + P.lam * P.q * P.δ := by nlinarith [mul_pos hlam hq]
  have hden1 : 0 < 1 - P.δ + P.lam * P.δ := by nlinarith
  have ha0 : 0 < A P := by unfold A; positivity
  have ha1 : A P < 1 := by unfold A; rw [div_lt_one hden]; nlinarith
  have hb0 : 0 < A1 P := by unfold A1; positivity
  have hb1 : A1 P < 1 := by unfold A1; rw [div_lt_one hden1]; nlinarith
  have hR := hrel P hP
  set u : ℕ → ℝ := fun x => P.δ * J x with hu
  have hG := geom u (A P) (A P * (P.v - p) + E) 0 X (Nat.zero_le _)
    (fun x _ hx => by simp only [hu]; rw [hEq x hx]; ring)
  have F1 : u 0 = A P * (P.v - p) + E + A P * u 1 := by
    simp only [hu]; rw [hEq 0 (by omega)]; ring
  have F3 : u X = A P * (P.v + P.k) + E + A P * u 0 := by
    simp only [hu]; rw [hEX]; ring
  have H31 : u 0 ≤ P.v - p + u 1 := h31
  have H32 : P.v + P.k + u 0 < P.vbar + u X := by
    have := h32; unfold RedeemsHigh at this; simp only [hu]; linarith
  simp only [Nat.sub_zero] at hG
  have hZ : A P ^ X < 1 := pow_lt_one₀ ha0.le ha1 (by omega)
  have hZ0 : 0 ≤ A P ^ X := by positivity
  unfold pdUpper pD
  simp only [Nat.sub_self, pow_zero, zero_add, pow_one, mul_one, sub_self, one_mul]
  rw [pow_succ]
  generalize A1 P = b at *
  generalize A P = a at *
  generalize a ^ X = Z at *
  have hZa : 0 ≤ 1 - Z * a := by nlinarith
  -- closed form: (1-a) u0 (1 - Z a) = (a(v-p)+E)(1-Z) + Z(1-a)(a(v+k)+E)
  have K2 : (1 - a) * u 0 * (1 - Z * a) =
      (a * (P.v - p) + E) * (1 - Z) + Z * (1 - a) * (a * (P.v + P.k) + E) := by
    linear_combination hG + Z * (1 - a) * F3
  constructor
  · -- from (31): E ≤ (1 - a) u0
    have K1 : E ≤ (1 - a) * u 0 := by
      have := mul_le_mul_of_nonneg_left H31 ha0.le
      linarith
    have K3 := mul_le_mul_of_nonneg_right K1 hZa
    rw [K2] at K3
    rw [le_div_iff₀ (by linarith)]
    have K4 : a * (p * (1 - Z)) ≤ a * ((1 - Z * a) * P.v + Z * (1 - a) * P.k) := by
      nlinarith
    exact le_of_mul_le_mul_left K4 ha0
  · -- from (32)
    have K1 : (1 - a) * (P.v + P.k) + (1 - a) * u 0 < P.vbar + E := by linarith
    have K3 := mul_lt_mul_of_pos_right K1 (show 0 < 1 - Z * a by nlinarith)
    have K3' : (1 - a) * (P.v + P.k) * (1 - Z * a) + (1 - a) * u 0 * (1 - Z * a) <
        (P.vbar + E) * (1 - Z * a) := by linarith
    rw [K2] at K3'
    have K4 : (1 - Z * a) * (P.v - P.vbar) + (1 - a) * P.k < a * p * (1 - Z) := by nlinarith
    have hden' : 0 < P.q * (1 - Z) * b := by
      have : 0 < 1 - Z := by linarith
      positivity
    rw [div_lt_iff₀ hden']
    have K5 : a * ((1 - b + P.q * (1 - Z) * b) * (P.v - P.vbar) + (1 - b) * P.k) =
        P.q * b * ((1 - Z * a) * (P.v - P.vbar) + (1 - a) * P.k) := by
      linear_combination (P.v - P.vbar + P.k) * hR
    have K6 : a * (p * (P.q * (1 - Z) * b)) = P.q * b * (a * p * (1 - Z)) := by ring
    have hqb : 0 < P.q * b := by positivity
    have K7 : a * ((1 - b + P.q * (1 - Z) * b) * (P.v - P.vbar) + (1 - b) * P.k) <
        a * (p * (P.q * (1 - Z) * b)) := by
      rw [K5, K6]; exact mul_lt_mul_of_pos_left K4 hqb
    exact lt_of_mul_lt_mul_left K7 ha0.le
