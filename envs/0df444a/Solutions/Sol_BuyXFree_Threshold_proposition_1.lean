-- Prove2me | solution 1 for BuyXFree.Threshold.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T16:49:26.975162+00:00
-- url     : https://prove2.me/submissions/52b715a4-81ed-4f2b-a52f-b703871c9062

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

namespace BuyXFree.Threshold.VFAux
open BuyXFree.Threshold

/-- The per-period gain `g(t) = λq·max(v − p + t, 0) + λ(1−q)·max(v − p + t, v̄)`, so that
`(1 − δ) J(x) = g(δ(J(x+1) − J(x)))`. -/
noncomputable def gf (P : Params) (p t : ℝ) : ℝ :=
  P.lam * P.q * max (P.v - p + t) 0 + P.lam * (1 - P.q) * max (P.v - p + t) P.vbar

lemma gf_mono (P : Params) (hP : P.Standing) (p : ℝ) {s t : ℝ} (h : s ≤ t) :
    gf P p s ≤ gf P p t := by
  obtain ⟨hl0, hl1, hq0, hq1, -⟩ := hP
  unfold gf
  have h1 : max (P.v - p + s) 0 ≤ max (P.v - p + t) 0 := max_le_max (by linarith) le_rfl
  have h2 : max (P.v - p + s) P.vbar ≤ max (P.v - p + t) P.vbar := max_le_max (by linarith) le_rfl
  have c1 : 0 ≤ P.lam * P.q := mul_nonneg hl0 hq0
  have c2 : 0 ≤ P.lam * (1 - P.q) := mul_nonneg hl0 (by linarith)
  have := mul_le_mul_of_nonneg_left h1 c1
  have := mul_le_mul_of_nonneg_left h2 c2
  linarith

lemma gf_lt (P : Params) (hP : P.Standing) (p : ℝ) {s t : ℝ} (h : gf P p s < gf P p t) :
    s < t := by
  by_contra hc
  exact absurd (gf_mono P hP p (not_lt.1 hc)) (not_le.2 h)

lemma hJx (P : Params) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (hJ : IsValueFn P p X J) (x : ℕ)
    (hx : x < X) : (1 - P.δ) * J x = gf P p (P.δ * (J (x + 1) - J x)) := by
  have h := hJ.1 x hx
  have e1 : max (P.v - p + P.δ * J (x + 1)) (P.δ * J x) =
      P.δ * J x + max (P.v - p + P.δ * (J (x + 1) - J x)) 0 := by
    rw [← max_add_add_left]; congr 1 <;> ring
  have e2 : max (P.v - p + P.δ * J (x + 1)) (P.vbar + P.δ * J x) =
      P.δ * J x + max (P.v - p + P.δ * (J (x + 1) - J x)) P.vbar := by
    rw [← max_add_add_left]; congr 1 <;> ring
  rw [e1, e2] at h
  unfold gf
  linear_combination h

lemma hJX (P : Params) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (hJ : IsValueFn P p X J) :
    (1 - P.δ) * J X = gf P p (P.δ * (J 0 - J X) + p + P.k) := by
  have h := hJ.2
  have e1 : max (P.v + P.k + P.δ * J 0) (P.δ * J X) =
      P.δ * J X + max (P.v - p + (P.δ * (J 0 - J X) + p + P.k)) 0 := by
    rw [← max_add_add_left]; congr 1 <;> ring
  have e2 : max (P.v + P.k + P.δ * J 0) (P.vbar + P.δ * J X) =
      P.δ * J X + max (P.v - p + (P.δ * (J 0 - J X) + p + P.k)) P.vbar := by
    rw [← max_add_add_left]; congr 1 <;> ring
  rw [e1, e2] at h
  unfold gf
  linear_combination h

/-- For a nonpositive threshold `c`, failing it propagates one step forward. -/
lemma step (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (J : ℕ → ℝ)
    (hJ : IsValueFn P p X J) (c : ℝ) (hc : c ≤ 0) (y : ℕ) (hy : y + 1 < X)
    (h : P.δ * (J (y + 1) - J y) < c) : P.δ * (J (y + 1 + 1) - J (y + 1)) < c := by
  have hd0 : 0 < P.δ := hP.2.2.2.2.1
  have hd1 : P.δ < 1 := hP.2.2.2.2.2.1
  have e1 := hJx P p X J hJ y (by omega)
  have e2 := hJx P p X J hJ (y + 1) hy
  have hneg : J (y + 1) - J y < 0 := by
    by_contra hn
    have : 0 ≤ P.δ * (J (y + 1) - J y) := mul_nonneg hd0.le (not_lt.1 hn)
    linarith
  have hm := gf_mono P hP p h.le
  have : (1 - P.δ) * (J (y + 1) - J y) < 0 := mul_neg_of_pos_of_neg (by linarith) hneg
  exact gf_lt P hP p (by linarith)

/-- Iterating `step`. -/
lemma steps (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (J : ℕ → ℝ)
    (hJ : IsValueFn P p X J) (c : ℝ) (hc : c ≤ 0) (y : ℕ)
    (h : P.δ * (J (y + 1) - J y) < c) :
    ∀ n, y + n < X → P.δ * (J (y + n + 1) - J (y + n)) < c := by
  intro n
  induction n with
  | zero => intro _; simpa using h
  | succ n ih =>
    intro hn
    have := step P hP p X J hJ c hc (y + n) (by omega) (ih (by omega))
    rwa [show y + (n + 1) = y + n + 1 by omega]

/-- For a nonpositive threshold `c ≤ p + k`, failing it in state `X − 1` forces failing it in
state `0`. -/
lemma wrap (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (hX : 1 ≤ X) (J : ℕ → ℝ)
    (hJ : IsValueFn P p X J) (c : ℝ) (hc : c ≤ 0) (hck : c ≤ p + P.k)
    (hlt : gf P p (P.δ * (J 0 - J X) + p + P.k) < gf P p c) :
    P.δ * (J 1 - J 0) < c := by
  have hd0 : 0 < P.δ := hP.2.2.2.2.1
  have hd1 : P.δ < 1 := hP.2.2.2.2.2.1
  have hX' := hJX P p X J hJ
  have h1 := gf_lt P hP p hlt
  have hneg : J 0 - J X < 0 := by
    by_contra hn
    have : 0 ≤ P.δ * (J 0 - J X) := mul_nonneg hd0.le (not_lt.1 hn)
    linarith
  have e0 := hJx P p X J hJ 0 (by omega)
  have : (1 - P.δ) * (J 0 - J X) < 0 := mul_neg_of_pos_of_neg (by linarith) hneg
  exact gf_lt P hP p (by simp only [zero_add] at e0; linarith)

/-- If a nonpositive threshold `c ≤ p + k` fails in state `X − 1`, the redemption analogue
fails too: `g(δ(J0 − JX) + p + k) < g(c)`. -/
lemma lastX (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (hX : 1 ≤ X) (J : ℕ → ℝ)
    (hJ : IsValueFn P p X J) (c : ℝ) (hc : c ≤ 0)
    (h : P.δ * (J X - J (X - 1)) < c) :
    gf P p (P.δ * (J 0 - J X) + p + P.k) < gf P p c := by
  have hd0 : 0 < P.δ := hP.2.2.2.2.1
  have hd1 : P.δ < 1 := hP.2.2.2.2.2.1
  have hX' := hJX P p X J hJ
  have e := hJx P p X J hJ (X - 1) (by omega)
  rw [Nat.sub_add_cancel hX] at e
  have hneg : J X - J (X - 1) < 0 := by
    by_contra hn
    have : 0 ≤ P.δ * (J X - J (X - 1)) := mul_nonneg hd0.le (not_lt.1 hn)
    linarith
  have hm := gf_mono P hP p h.le
  have : (1 - P.δ) * (J X - J (X - 1)) < 0 := mul_neg_of_pos_of_neg (by linarith) hneg
  linarith

/-- Core monotonicity: for every threshold `c` with `c > 0` or `c ≤ min 0 (p + k)`,
`δ(J(x+1) − J(x)) ≥ c` implies `δ(J(x+2) − J(x+1)) ≥ c` for `x + 2 ≤ X`. -/
lemma core (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (hX : 1 ≤ X) (J : ℕ → ℝ)
    (hJ : IsValueFn P p X J) (c : ℝ) (hck : 0 < c ∨ (c ≤ 0 ∧ c ≤ p + P.k))
    (x : ℕ) (hx : x + 2 ≤ X) (h : c ≤ P.δ * (J (x + 1) - J x)) :
    c ≤ P.δ * (J (x + 2) - J (x + 1)) := by
  have hd0 : 0 < P.δ := hP.2.2.2.2.1
  have hd1 : P.δ < 1 := hP.2.2.2.2.2.1
  by_contra hcon
  push Not at hcon
  rcases hck with hc | ⟨hc, hck⟩
  · have e1 := hJx P p X J hJ x (by omega)
    have e2 := hJx P p X J hJ (x + 1) (by omega)
    have hpos : 0 < J (x + 1) - J x := by
      by_contra hn
      have : P.δ * (J (x + 1) - J x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hd0.le (not_lt.1 hn)
      linarith
    have hm := gf_mono P hP p h
    have hm2 := gf_mono P hP p hcon.le
    have : 0 < (1 - P.δ) * (J (x + 1) - J x) := mul_pos (by linarith) hpos
    rw [show x + 2 = x + 1 + 1 by omega] at hm2
    linarith
  · -- propagate from x+1 up to X-1, wrap around, and come back to x
    have hfwd := steps P hP p X J hJ c hc (x + 1)
      (by rw [show x + 1 + 1 = x + 2 by omega]; exact hcon) (X - 1 - (x + 1)) (by omega)
    rw [show x + 1 + (X - 1 - (x + 1)) = X - 1 by omega, Nat.sub_add_cancel hX] at hfwd
    have hl := lastX P hP p X hX J hJ c hc hfwd
    have h0 := wrap P hP p X hX J hJ c hc hck hl
    have hback := steps P hP p X J hJ c hc 0 (by simpa using h0) x (by omega)
    simp only [zero_add] at hback
    linarith


/-- Monotonicity for `p + k ≥ 0`: `J(x) ≤ J(x+1)` for `x < X`. -/
lemma mono (P : Params) (hP : P.Standing) (p : ℝ) (hpk : 0 ≤ p + P.k) (X : ℕ) (hX : 1 ≤ X)
    (J : ℕ → ℝ) (hJ : IsValueFn P p X J) : ∀ y < X, J y ≤ J (y + 1) := by
  have hd0 : 0 < P.δ := hP.2.2.2.2.1
  intro y hy
  by_contra hcon
  push Not at hcon
  have hneg : P.δ * (J (y + 1) - J y) < 0 := mul_neg_of_pos_of_neg hd0 (by linarith)
  have hfwd := steps P hP p X J hJ 0 le_rfl y hneg (X - 1 - y) (by omega)
  rw [show y + (X - 1 - y) = X - 1 by omega, Nat.sub_add_cancel hX] at hfwd
  have hl := lastX P hP p X hX J hJ 0 le_rfl hfwd
  have h0 := wrap P hP p X hX J hJ 0 le_rfl (by linarith) hl
  have hall := steps P hP p X J hJ 0 le_rfl 0 (by simpa using h0)
  -- J decreases along 0, 1, …, X
  have hdec : ∀ n, n ≤ X → J n ≤ J 0 := by
    intro n
    induction n with
    | zero => intro _; exact le_rfl
    | succ n ih =>
      intro hn
      have := hall n (by omega)
      simp only [zero_add] at this
      have : J (n + 1) - J n < 0 := by
        by_contra h'
        have : 0 ≤ P.δ * (J (n + 1) - J n) := mul_nonneg hd0.le (not_lt.1 h')
        linarith
      linarith [ih (by omega)]
  have hXle := hdec X le_rfl
  have hDX := gf_lt P hP p hl
  have : J 0 - J X < 0 := by
    by_contra h'
    have : 0 ≤ P.δ * (J 0 - J X) := mul_nonneg hd0.le (not_lt.1 h')
    linarith
  linarith

/-- Convexity for `p + k ≥ 0`. -/
lemma convex (P : Params) (hP : P.Standing) (p : ℝ) (hpk : 0 ≤ p + P.k) (X : ℕ) (hX : 1 ≤ X)
    (J : ℕ → ℝ) (hJ : IsValueFn P p X J) (x : ℕ) (hx : x + 2 ≤ X) :
    J (x + 1) - J x ≤ J (x + 2) - J (x + 1) := by
  have hd0 : 0 < P.δ := hP.2.2.2.2.1
  have hd1 : P.δ < 1 := hP.2.2.2.2.2.1
  have hm := mono P hP p hpk X hX J hJ
  have h1 := hm x (by omega)
  have h2 := hm (x + 1) (by omega)
  by_contra hcon
  push Not at hcon
  have e1 := hJx P p X J hJ x (by omega)
  have e2 := hJx P p X J hJ (x + 1) (by omega)
  rw [show x + 1 + 1 = x + 2 by omega] at e2
  have hle : P.δ * (J (x + 2) - J (x + 1)) ≤ P.δ * (J (x + 1) - J x) :=
    mul_le_mul_of_nonneg_left hcon.le hd0.le
  have hg := gf_mono P hP p hle
  -- g(D_{x+1}) = g(D_x) + (1-δ)(J(x+1) - J x) ≤ g(D_x) forces J(x+1) = J x
  have : (1 - P.δ) * (J (x + 1) - J x) ≤ 0 := by linarith
  have : J (x + 1) - J x ≤ 0 := by
    by_contra h'
    have : 0 < (1 - P.δ) * (J (x + 1) - J x) := mul_pos (by linarith) (not_le.1 h')
    linarith
  linarith

end BuyXFree.Threshold.VFAux

open BuyXFree.Threshold BuyXFree.Threshold.VFAux in
theorem solution (P : Params) (hP : P.Standing) (p : ℝ) (hp : 0 ≤ p) (X : ℕ) (hX : 1 ≤ X)
    (J : ℕ → ℝ) (hJ : IsValueFn P p X J) :
    (∀ x < X, J x ≤ J (x + 1)) ∧
      ∀ x : ℕ, x + 2 ≤ X → J (x + 1) - J x ≤ J (x + 2) - J (x + 1) := by
  have hpk : 0 ≤ p + P.k := by have := hP.2.2.2.2.2.2.2.2; linarith
  exact ⟨mono P hP p hpk X hX J hJ, fun x hx => convex P hP p hpk X hX J hJ x hx⟩
