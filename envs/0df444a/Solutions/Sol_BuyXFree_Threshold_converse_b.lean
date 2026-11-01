-- Prove2me | solution 1 for BuyXFree.Threshold.converse_b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T16:44:19.338709+00:00
-- url     : https://prove2.me/submissions/ab24ffa2-2363-4ead-8dde-1b2fc22f57fc

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
    (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (hJ : IsValueFn P p X J)
    (τ : ℕ) (hτ1 : 1 ≤ τ) (hτX : τ + 1 ≤ X)
    (h25 : BuysLow P p J 0) (h26 : BuysHigh P p J τ) (h27 : ¬ BuysHigh P p J (τ - 1)) :
    p ≤ pB P X τ ∧ p ≤ pD P X τ ∧ pD P X (τ - 1) < p := by
  have hX : 1 ≤ X := by omega
  have hP' := hP
  obtain ⟨hl0, hl1, hq0, hq1, hd0, hd1, hvb0, hvbv, hk0⟩ := hP'
  have hBL : ∀ x < X, BuysLow P p J x := by
    intro x hx
    induction x with
    | zero => exact h25
    | succ n ih => exact (corollary_1 P hP p X hX J hJ n (by omega)).1 (ih (by omega))
  have hRL : RedeemsLow P X J := by
    have := lemma_4 P hP p X hX J hJ; unfold RedeemsLow; linarith
  have hup : ∀ x, BuysHigh P p J x → ∀ n, x + n < X → BuysHigh P p J (x + n) := by
    intro x hb n
    induction n with
    | zero => intro _; exact hb
    | succ n ih =>
      intro hn
      exact (corollary_1 P hP p X hX J hJ (x + n) (by omega)).2 (ih (by omega))
  have hBH : ∀ x, τ ≤ x → x < X → BuysHigh P p J x := by
    intro x h1 h2
    have := hup τ h26 (x - τ) (by omega)
    rwa [show τ + (x - τ) = x by omega] at this
  have hnBH : ∀ x < τ, ¬ BuysHigh P p J x := by
    intro x hx hb
    apply h27
    have := hup x hb (τ - 1 - x) (by omega)
    rwa [show x + (τ - 1 - x) = τ - 1 by omega] at this
  have hRH : RedeemsHigh P X J := by
    have h := hBH (X - 1) (by omega) (by omega)
    unfold BuysHigh at h
    rw [Nat.sub_add_cancel hX] at h
    have := lemma_5 P hP p X hX J hJ (by linarith)
    unfold RedeemsHigh; linarith
  set E := P.lam * (1 - P.q) * P.δ * P.vbar / (1 - P.δ + P.lam * P.q * P.δ) with hE
  have hEqL : ∀ x < τ, P.δ * J x = A P * (P.v - p + P.δ * J (x + 1)) + E := by
    intro x hx
    have h := hJ.1 x (by omega)
    have hb := hnBH x hx
    have hl := hBL x (by omega)
    unfold BuysHigh at hb
    unfold BuysLow at hl
    rw [max_eq_left hl, max_eq_right (le_of_lt (not_le.1 hb))] at h
    exact eq_low P hP _ _ h
  have hEqB : ∀ x, τ ≤ x → x < X → P.δ * J x = A1 P * (P.v - p + P.δ * J (x + 1)) := by
    intro x h1 h2
    have h := hJ.1 x h2
    have hb := hBH x h1 h2
    unfold BuysHigh at hb
    rw [max_eq_left (by linarith), max_eq_left hb] at h
    exact eq_both P hP _ _ h
  have hEX : P.δ * J X = A1 P * (P.v + P.k + P.δ * J 0) := by
    have h := hJ.2
    have hb := hRH
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
  have hG1 := geom u (A P) (A P * (P.v - p) + E) 0 τ (Nat.zero_le _)
    (fun x _ hx => by simp only [hu]; rw [hEqL x hx]; ring)
  have hG2 := geom u (A1 P) (A1 P * (P.v - p)) τ X (by omega)
    (fun x h1 h2 => by simp only [hu]; rw [hEqB x h1 h2]; ring)
  have F1 : u 0 = A P * (P.v - p) + E + A P * u 1 := by
    simp only [hu]; rw [hEqL 0 (by omega)]; ring
  have Ft : u τ = A1 P * (P.v - p) + A1 P * u (τ + 1) := by
    simp only [hu]; rw [hEqB τ le_rfl (by omega)]; ring
  have Ftm : u (τ - 1) = A P * (P.v - p) + E + A P * u τ := by
    simp only [hu]; rw [hEqL (τ - 1) (by omega), Nat.sub_add_cancel hτ1]; ring
  have F3 : u X = A1 P * (P.v + P.k) + A1 P * u 0 := by
    simp only [hu]; rw [hEX]; ring
  have H25 : u 0 ≤ P.v - p + u 1 := h25
  have H26 : P.vbar + u τ ≤ P.v - p + u (τ + 1) := h26
  have H27 : P.v - p + u τ < P.vbar + u (τ - 1) := by
    have := h27; unfold BuysHigh at this; rw [Nat.sub_add_cancel hτ1] at this
    simp only [hu]; linarith
  simp only [Nat.sub_zero] at hG1
  have hZa : A P ^ τ < 1 := pow_lt_one₀ ha0.le ha1 (by omega)
  have hZa0 : 0 < A P ^ τ := by positivity
  have hZb : A1 P ^ (X - τ) < 1 := pow_lt_one₀ hb0.le hb1 (by omega)
  have hZb0 : 0 < A1 P ^ (X - τ) := by positivity
  have hW : A P ^ τ = A P ^ (τ - 1) * A P := by
    rw [← pow_succ, Nat.sub_add_cancel hτ1]
  have hW1 : A P ^ (τ - 1) ≤ 1 := pow_le_one₀ ha0.le ha1.le
  unfold pB pD
  rw [show X - (τ - 1) + 1 = (X - τ) + 2 by omega, show X - (τ - 1) = (X - τ) + 1 by omega,
    pow_add, pow_add, pow_one]
  generalize A1 P = b at *
  generalize A P ^ (τ - 1) = Wa at *
  generalize A P ^ τ = Za at *
  generalize A P = a at *
  generalize b ^ (X - τ) = Zb at *
  generalize u 0 = u0 at *
  generalize u 1 = u1 at *
  generalize u X = uX at *
  generalize u (τ - 1) = utm1 at *
  generalize u (τ + 1) = ut1 at *
  generalize u τ = ut at *
  generalize P.q = q at *
  generalize P.v = v at *
  generalize P.vbar = vb at *
  generalize P.k = k at *
  have hkap : 0 < (b * (1 - a) * (1 - b)) := by
    have : 0 < 1 - a := by linarith
    have : 0 < 1 - b := by linarith
    positivity
  have hDt : 0 < (a * b * (1 - a) * (1 - b) * (1 - Za * Zb * b)) := by
    have : 0 < 1 - a := by linarith
    have : 0 < 1 - b := by linarith
    have : Za * Zb * b < 1 := by
      have e1 : Za * Zb ≤ Za := mul_le_of_le_one_right hZa0.le hZb.le
      have e2 : Za * Zb * b ≤ Za * Zb := mul_le_of_le_one_right (by positivity) hb1.le
      linarith
    have : 0 < 1 - Za * Zb * b := by linarith
    positivity
  have h1a : 0 < 1 - a := by linarith
  have h1b : 0 < 1 - b := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have key : (b * (1 - a) * (1 - b)) * (b ^ 2 * (1 - a) ^ 2) * ((q * (1 - Za * (Zb * b)) * v + (1 - q) * Za * (1 - Zb * b) * (v - vb) + Za * Zb * (1 - b) * k) - p * (Za * (1 - Zb) + q * (1 - Za))) =
        (b * (1 - a) * (1 - b)) * (a * b * (1 - a) * (1 - b) * (1 - Za * Zb * b)) * (v - p + u1 - u0) := by
      linear_combination (-b^2*(a - 1)^2*(b - 1)^2) * hG1 + (-Za*b^2*(a - 1)^3*(b - 1)) * hG2 + (Za*Zb*b^2*(a - 1)^3*(b - 1)^2) * F3 + (-b^2*(a - 1)^2*(b - 1)^2*(Za*Zb*b - 1)) * F1 + (b^2*(a - 1)^2*(b - 1)*(-E*Zb*b^2 + E*Zb*b + E*b - E - Zb*a*b^2*q*vb + Zb*a*b^2*vb + Zb*b^2*q*vb - Zb*b^2*vb + a*b*p*q - a*b*p - a*b*q*v + a*b*q*vb + a*b*v - a*b*vb + a*p - a*v - b*p*q + b*q*v - b*q*vb + b*vb)) * hW + (Wa*a*b^2*(a - 1)^2*(b - 1)*(Zb*b - 1)) * hR2 + (b^2*(a - 1)^2*(b - 1)*(p - v)*(Wa*a - 1)) * hR
    have hs : 0 ≤ (b * (1 - a) * (1 - b)) * (a * b * (1 - a) * (1 - b) * (1 - Za * Zb * b)) * (v - p + u1 - u0) :=
      mul_nonneg (mul_pos hkap hDt).le (by linarith)
    rw [← key] at hs
    have hpos : 0 < (b * (1 - a) * (1 - b)) * (b ^ 2 * (1 - a) ^ 2) := by positivity
    have hT := (mul_nonneg_iff_of_pos_left hpos).1 hs
    have hd : 0 < (Za * (1 - Zb) + q * (1 - Za)) := by
      have : 0 < 1 - Zb := by linarith
      have : 0 < 1 - Za := by linarith
      positivity
    rw [le_div_iff₀ hd]
    linarith
  · have key : (b * (1 - a) * (1 - b)) * (a * b * (1 - a) * (1 - b)) * (((1 - Zb * b + q * (1 - Za) * (Zb * b)) * (v - vb) + Zb * (1 - b) * k) - p * (1 - Zb + q * (1 - Za) * (Zb * b))) =
        (b * (1 - a) * (1 - b)) * (a * b * (1 - a) * (1 - b) * (1 - Za * Zb * b)) * (v - p + ut1 - vb - ut) := by
      linear_combination (-Zb*a*b^2*(a - 1)*(b - 1)^3) * hG1 + (-a*b*(a - 1)^2*(b - 1)^2) * hG2 + (Zb*a*b*(a - 1)^2*(b - 1)^3) * F3 + (-a*b*(a - 1)^2*(b - 1)^2*(Za*Zb*b - 1)) * Ft + (Zb*a*b^2*(a - 1)*(b - 1)^2*(E*b - E + a*b*p*q - a*b*p - a*b*q*v + a*b*q*vb + a*b*v - a*b*vb + a*p - a*v - b*p*q + b*q*v - b*q*vb + b*vb)) * hW + (-Zb*a*b^2*(a - 1)*(b - 1)^2*(Wa*a - 1)) * hR2 + (Zb*a*b^2*(a - 1)*(b - 1)^2*(p - v)*(Wa*a - 1)) * hR
    have hs : 0 ≤ (b * (1 - a) * (1 - b)) * (a * b * (1 - a) * (1 - b) * (1 - Za * Zb * b)) * (v - p + ut1 - vb - ut) :=
      mul_nonneg (mul_pos hkap hDt).le (by linarith)
    rw [← key] at hs
    have hpos : 0 < (b * (1 - a) * (1 - b)) * (a * b * (1 - a) * (1 - b)) := by positivity
    have hT := (mul_nonneg_iff_of_pos_left hpos).1 hs
    have hd : 0 < (1 - Zb + q * (1 - Za) * (Zb * b)) := by
      have : 0 < 1 - Zb := by linarith
      have : 0 < 1 - Za := by linarith
      have : 0 ≤ q * (1 - Za) * (Zb * b) := by positivity
      linarith
    rw [le_div_iff₀ hd]
    linarith
  · have key : (b * (1 - a) * (1 - b)) * (a * b * (1 - a) ^ 2) * (p * (1 - Zb * b + q * (1 - Wa) * (Zb * b ^ 2)) - ((1 - Zb * b ^ 2 + q * (1 - Wa) * (Zb * b ^ 2)) * (v - vb) + Zb * b * (1 - b) * k)) =
        (b * (1 - a) * (1 - b)) * (a * b * (1 - a) * (1 - b) * (1 - Za * Zb * b)) * (vb + utm1 - (v - p + ut)) := by
      linear_combination (Zb*a*b^3*(a - 1)^2*(b - 1)^2) * hG1 + (a*b^2*(a - 1)^3*(b - 1)) * hG2 + (-Zb*a*b^2*(a - 1)^3*(b - 1)^2) * F3 + (a*b^2*(a - 1)^2*(b - 1)^2*(Za*Zb*b - 1)) * Ftm + (Zb*a*b^3*(a - 1)^2*(b - 1)^2*(p - v + vb)) * hW + (-a*b^2*(a - 1)^2*(b - 1)*(Zb*b - 1)) * hR2 + (-a*b^2*(a - 1)^2*(b - 1)*(Wa*Zb*b*p - Wa*Zb*b*v + Wa*Zb*b*vb - Zb*b*p + Zb*b*v - vb)) * hR
    have hs : 0 < (b * (1 - a) * (1 - b)) * (a * b * (1 - a) * (1 - b) * (1 - Za * Zb * b)) * (vb + utm1 - (v - p + ut)) :=
      mul_pos (mul_pos hkap hDt) (by linarith)
    rw [← key] at hs
    have hpos : 0 < (b * (1 - a) * (1 - b)) * (a * b * (1 - a) ^ 2) := by positivity
    have hT := (mul_pos_iff_of_pos_left hpos).1 hs
    have hd : 0 < (1 - Zb * b + q * (1 - Wa) * (Zb * b ^ 2)) := by
      have : Zb * b < 1 := by
        have := mul_le_of_le_one_right hZb0.le hb1.le
        linarith
      have : 0 ≤ q * (1 - Wa) * (Zb * b ^ 2) := by
        have : 0 ≤ 1 - Wa := by linarith
        positivity
      linarith
    rw [div_lt_iff₀ hd]
    linarith
