-- Prove2me | solution 1 for BuyXFree.Threshold.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T17:03:09.712295+00:00
-- url     : https://prove2.me/submissions/36098f0c-a1fc-44a0-9df1-66bcf0a3b9f0

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model
import Theorems.Thm_BuyXFree_Threshold_corollary_1
import Theorems.Thm_BuyXFree_Threshold_lemma_4
import Theorems.Thm_BuyXFree_Threshold_lemma_5
import Theorems.Thm_BuyXFree_Threshold_converse_a
import Theorems.Thm_BuyXFree_Threshold_converse_b
import Theorems.Thm_BuyXFree_Threshold_converse_c
import Theorems.Thm_BuyXFree_Threshold_converse_d

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


lemma max_sub_max_ge (a1 a2 b1 b2 m : ℝ) (h1 : m ≤ a1 - b1) (h2 : m ≤ a2 - b2) :
    m ≤ max a1 a2 - max b1 b2 := by
  rcases le_total b1 b2 with h | h
  · rw [max_eq_right h]
    have := le_max_right a1 a2
    linarith
  · rw [max_eq_left h]
    have := le_max_left a1 a2
    linarith

/-- Right-hand side of the optimality equations, evaluated on an arbitrary `V`. -/
noncomputable def bell (P : Params) (p : ℝ) (X : ℕ) (V : ℕ → ℝ) (x : ℕ) : ℝ :=
  if x < X then
    P.lam * P.q * max (P.v - p + P.δ * V (x + 1)) (P.δ * V x)
      + P.lam * (1 - P.q) * max (P.v - p + P.δ * V (x + 1)) (P.vbar + P.δ * V x)
      + (1 - P.lam) * P.δ * V x
  else
    P.lam * P.q * max (P.v + P.k + P.δ * V 0) (P.δ * V X)
      + P.lam * (1 - P.q) * max (P.v + P.k + P.δ * V 0) (P.vbar + P.δ * V X)
      + (1 - P.lam) * P.δ * V X

/-- Comparison: a sub-solution of the optimality equations lies below `J`. -/
lemma comp (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (J : ℕ → ℝ)
    (hJ : IsValueFn P p X J) (V : ℕ → ℝ) (hV : ∀ x ≤ X, V x ≤ bell P p X V x) :
    ∀ y ≤ X, V y ≤ J y := by
  obtain ⟨hl0, hl1, hq0, hq1, hd0, hd1, -⟩ := hP
  obtain ⟨y0, hy0, hmin⟩ := (Finset.range (X + 1)).exists_min_image (fun y => J y - V y)
    ⟨0, by simp⟩
  have hy0' : y0 ≤ X := by simpa [Nat.lt_succ_iff] using hy0
  set m := J y0 - V y0 with hm
  have hmin' : ∀ y ≤ X, m ≤ J y - V y := fun y hy =>
    hmin y (by simp [Nat.lt_succ_iff]; omega)
  suffices h : 0 ≤ m by
    intro y hy; have := hmin' y hy; linarith
  by_contra hneg
  push Not at hneg
  have hVy := hV y0 hy0'
  have c1 : 0 ≤ P.lam * P.q := mul_nonneg hl0 hq0
  have c2 : 0 ≤ P.lam * (1 - P.q) := mul_nonneg hl0 (by linarith)
  have c3 : 0 ≤ (1 - P.lam) * P.δ := mul_nonneg (by linarith) hd0.le
  have hδm : P.δ * m ≤ P.δ * (J y0 - V y0) := le_of_eq (by rw [hm])
  unfold bell at hVy
  by_cases hlt : y0 < X
  · rw [if_pos hlt] at hVy
    have hJy := hJ.1 y0 hlt
    have hn := hmin' (y0 + 1) (by omega)
    have d1 : P.δ * m ≤ (P.v - p + P.δ * J (y0 + 1)) - (P.v - p + P.δ * V (y0 + 1)) := by
      have := mul_le_mul_of_nonneg_left hn hd0.le; linarith
    have d2 : P.δ * m ≤ P.δ * J y0 - P.δ * V y0 := by
      have := mul_le_mul_of_nonneg_left (hmin' y0 hy0') hd0.le; linarith
    have d3 : P.δ * m ≤ (P.vbar + P.δ * J y0) - (P.vbar + P.δ * V y0) := by linarith
    have e1 := max_sub_max_ge _ _ _ _ _ d1 d2
    have e2 := max_sub_max_ge _ _ _ _ _ d1 d3
    have f1 := mul_le_mul_of_nonneg_left e1 c1
    have f2 := mul_le_mul_of_nonneg_left e2 c2
    have f3 := mul_le_mul_of_nonneg_left d2 c3
    have : m ≤ P.δ * m := by nlinarith
    nlinarith
  · rw [if_neg hlt] at hVy
    have hyX : y0 = X := by omega
    rw [hyX] at hVy hm
    have hJy := hJ.2
    have hn := hmin' 0 (by omega)
    have d1 : P.δ * m ≤ (P.v + P.k + P.δ * J 0) - (P.v + P.k + P.δ * V 0) := by
      have := mul_le_mul_of_nonneg_left hn hd0.le; linarith
    have d2 : P.δ * m ≤ P.δ * J X - P.δ * V X := by
      have := mul_le_mul_of_nonneg_left (hmin' X le_rfl) hd0.le; linarith
    have d3 : P.δ * m ≤ (P.vbar + P.δ * J X) - (P.vbar + P.δ * V X) := by linarith
    have e1 := max_sub_max_ge _ _ _ _ _ d1 d2
    have e2 := max_sub_max_ge _ _ _ _ _ d1 d3
    have f1 := mul_le_mul_of_nonneg_left e1 c1
    have f2 := mul_le_mul_of_nonneg_left e2 c2
    have f3 := mul_le_mul_of_nonneg_left d2 c3
    have : m ≤ P.δ * m := by nlinarith
    nlinarith

/-- Backward coefficients for a cyclic linear recursion. -/
def coefAB (α β : ℕ → ℝ) (X : ℕ) : ℕ → ℝ × ℝ
  | 0 => (α X, β X)
  | n + 1 => (α (X - (n + 1)) + β (X - (n + 1)) * (coefAB α β X n).1,
      β (X - (n + 1)) * (coefAB α β X n).2)

/-- Solvability of `U x = α x + β x U(x+1)` (`x < X`), `U X = α X + β X U 0`, when
`0 ≤ β < 1`. -/
lemma exists_sol (α β : ℕ → ℝ) (X : ℕ) (hβ : ∀ x, 0 ≤ β x ∧ β x < 1) :
    ∃ U : ℕ → ℝ, (∀ x < X, U x = α x + β x * U (x + 1)) ∧ U X = α X + β X * U 0 := by
  have hB : ∀ n, 0 ≤ (coefAB α β X n).2 ∧ (coefAB α β X n).2 < 1 := by
    intro n
    induction n with
    | zero => exact hβ X
    | succ n ih =>
      simp only [coefAB]
      obtain ⟨h1, h2⟩ := hβ (X - (n + 1))
      refine ⟨mul_nonneg h1 ih.1, ?_⟩
      calc β (X - (n + 1)) * (coefAB α β X n).2 ≤ β (X - (n + 1)) * 1 :=
            mul_le_mul_of_nonneg_left ih.2.le h1
        _ < 1 := by linarith
  set A := fun x => (coefAB α β X (X - x)).1
  set B := fun x => (coefAB α β X (X - x)).2
  have hB0 := hB X
  set u0 := A 0 / (1 - B 0) with hu0
  refine ⟨fun x => A x + B x * u0, fun x hx => ?_, ?_⟩
  · have e : X - x = (X - (x + 1)) + 1 := by omega
    have e2 : X - ((X - (x + 1)) + 1) = x := by omega
    simp only [A, B, e, coefAB, e2]
    ring_nf
  · have h0 : A 0 + B 0 * u0 = u0 := by
      have : (1 : ℝ) - B 0 ≠ 0 := by simp only [B]; rw [Nat.sub_zero]; linarith [hB0.2]
      rw [hu0]; field_simp; ring
    simp only [A, B, Nat.sub_self, coefAB] at h0 ⊢
    rw [h0]

noncomputable def Eb (P : Params) : ℝ :=
  P.lam * (1 - P.q) * P.δ * P.vbar / (1 - P.δ + P.lam * P.q * P.δ)

lemma basics (P : Params) (hP : P.Standing) (hlam : 0 < P.lam) (hq : 0 < P.q) :
    0 < A P ∧ A P < 1 ∧ 0 < A1 P ∧ A1 P < 1 ∧
      A P * (1 - A1 P) = P.q * A1 P * (1 - A P) ∧
      (1 - A1 P) * Eb P = A1 P * (1 - A P) * (1 - P.q) * P.vbar := by
  obtain ⟨hl0, hl1, hq0, hq1, hd0, hd1, hvb0, hvbv, hk0⟩ := hP
  have hden : 0 < 1 - P.δ + P.lam * P.q * P.δ := by nlinarith [mul_pos hlam hq]
  have hden1 : 0 < 1 - P.δ + P.lam * P.δ := by nlinarith
  have ha0 : 0 < A P := by unfold A; positivity
  have ha1 : A P < 1 := by unfold A; rw [div_lt_one hden]; nlinarith
  have hb0 : 0 < A1 P := by unfold A1; positivity
  have hb1 : A1 P < 1 := by unfold A1; rw [div_lt_one hden1]; nlinarith
  have hR := hrel P ⟨hl0, hl1, hq0, hq1, hd0, hd1, hvb0, hvbv, hk0⟩
  have hqE : Eb P * P.q = A P * (1 - P.q) * P.vbar := by unfold Eb A; ring
  refine ⟨ha0, ha1, hb0, hb1, hR, ?_⟩
  have h : P.q * ((1 - A1 P) * Eb P - A1 P * (1 - A P) * (1 - P.q) * P.vbar) = 0 := by
    linear_combination (1 - A1 P) * hqE + (1 - P.q) * P.vbar * hR
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h hq.ne'
  · linarith

/-- Reverse of `eq_both`. -/
lemma of_both (P : Params) (hP : P.Standing) (B Vx : ℝ) (h : P.δ * Vx = A1 P * B) :
    Vx = P.lam * P.q * B + P.lam * (1 - P.q) * B + (1 - P.lam) * P.δ * Vx := by
  obtain ⟨hl0, hl1, hq0, hq1, hd0, hd1, -⟩ := hP
  have hden : 0 < 1 - P.δ + P.lam * P.δ := by nlinarith
  unfold A1 at h
  rw [div_mul_eq_mul_div, eq_div_iff hden.ne'] at h
  have : P.δ * (Vx * (1 - P.δ + P.lam * P.δ) - P.lam * B) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h' | h'
  · exact absurd h' hd0.ne'
  · linear_combination h'

/-- Reverse of `eq_low`. -/
lemma of_low (P : Params) (hP : P.Standing) (B Vx : ℝ) (h : P.δ * Vx = A P * B + Eb P) :
    Vx = P.lam * P.q * B + P.lam * (1 - P.q) * (P.vbar + P.δ * Vx)
      + (1 - P.lam) * P.δ * Vx := by
  obtain ⟨hl0, hl1, hq0, hq1, hd0, hd1, -⟩ := hP
  have hden : 0 < 1 - P.δ + P.lam * P.q * P.δ := by
    have : 0 ≤ P.lam * P.q * P.δ := by positivity
    linarith
  unfold A Eb at h
  rw [div_mul_eq_mul_div, ← add_div, eq_div_iff hden.ne'] at h
  have : P.δ * (Vx * (1 - P.δ + P.lam * P.q * P.δ) - P.lam * P.q * B
      - P.lam * (1 - P.q) * P.vbar) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h' | h'
  · exact absurd h' hd0.ne'
  · linear_combination h'

/-- If a sub-solution `V` of the optimality equations has `W ≤ V(0)` and buys in state `0`
against the low option, then so does `J`. -/
lemma bl0_of_sub (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (hX : 1 ≤ X) (J : ℕ → ℝ)
    (hJ : IsValueFn P p X J) (V : ℕ → ℝ) (hV : ∀ x ≤ X, V x ≤ bell P p X V x)
    (hW : P.lam * (1 - P.q) * P.vbar ≤ (1 - P.δ) * V 0)
    (hB : P.δ * V 0 ≤ P.v - p + P.δ * V 1) : BuysLow P p J 0 := by
  have hP' := hP
  obtain ⟨hl0, hl1, hq0, hq1, hd0, hd1, hvb0, hvbv, hk0⟩ := hP'
  by_contra hn
  have hn' : ¬ BuysHigh P p J 0 := fun h => hn (by unfold BuysHigh at h; unfold BuysLow; linarith)
  unfold BuysLow at hn
  unfold BuysHigh at hn'
  have h := hJ.1 0 (by omega)
  rw [max_eq_right (le_of_lt (not_le.1 hn)), max_eq_right (le_of_lt (not_le.1 hn'))] at h
  have hc := comp P hP p X J hJ V hV
  have h1 := hc 1 hX
  have h0 : J 0 ≤ V 0 := by
    have : (1 - P.δ) * J 0 ≤ (1 - P.δ) * V 0 := by linarith
    exact le_of_mul_le_mul_left this (by linarith)
  have := mul_le_mul_of_nonneg_left h1 hd0.le
  have := mul_le_mul_of_nonneg_left h0 hd0.le
  simp only [zero_add] at hn
  linarith

/-- Reverse of the proof of Lemma 6. -/
lemma rev_a (P : Params) (hP : P.Standing) (hlam : 0 < P.lam) (hq : 0 < P.q) (p : ℝ) (X : ℕ)
    (hX : 1 ≤ X) (U : ℕ → ℝ)
    (hEq : ∀ x < X, U x = A1 P * (P.v - p) + A1 P * U (x + 1))
    (hEX : U X = A1 P * (P.v + P.k) + A1 P * U 0) (hp : p ≤ pD P X 0) :
    P.vbar + U 0 ≤ P.v - p + U 1 := by
  obtain ⟨-, -, hb0, hb1, -, -⟩ := basics P hP hlam hq
  have hG := geom U (A1 P) (A1 P * (P.v - p)) 0 X (Nat.zero_le _)
    (fun x _ hx => by rw [hEq x hx])
  have F1 := hEq 0 (by omega)
  simp only [zero_add] at F1
  simp only [Nat.sub_zero] at hG
  unfold pD at hp
  simp only [pow_zero, sub_self, mul_zero, zero_mul, add_zero, Nat.sub_zero] at hp
  have hZ : A1 P ^ X < 1 := pow_lt_one₀ hb0.le hb1 (by omega)
  rw [le_div_iff₀ (by linarith), pow_succ] at hp
  have hZ0 : 0 ≤ A1 P ^ X := by positivity
  generalize A1 P = b at *
  generalize b ^ X = Z at *
  have K2 : (1 - b) * U 0 * (1 - Z * b) =
      b * (P.v - p) * (1 - Z) + Z * b * (1 - b) * (P.v + P.k) := by
    linear_combination hG + Z * (1 - b) * hEX
  have hZb : 0 < 1 - Z * b := by nlinarith
  have K3 : b * P.vbar * (1 - Z * b) ≤ (1 - b) * U 0 * (1 - Z * b) := by
    rw [K2]; nlinarith
  have K1 : b * P.vbar ≤ (1 - b) * U 0 := le_of_mul_le_mul_right K3 hZb
  have : b * (P.vbar + U 0) ≤ b * (P.v - p + U 1) := by nlinarith
  exact le_of_mul_le_mul_left this hb0

/-- Reverse of the proof of Lemma 9. -/
lemma rev_d (P : Params) (hP : P.Standing) (hlam : 0 < P.lam) (hq : 0 < P.q) (p : ℝ) (X : ℕ)
    (hX : 1 ≤ X) (U : ℕ → ℝ)
    (hEq : ∀ x < X, U x = A P * (P.v - p) + Eb P + A P * U (x + 1))
    (hEX : U X = A P * (P.v + P.k) + Eb P + A P * U 0) (hp : p ≤ pdUpper P X) :
    U 0 ≤ P.v - p + U 1 := by
  obtain ⟨ha0, ha1, -, -, -, -⟩ := basics P hP hlam hq
  have hG := geom U (A P) (A P * (P.v - p) + Eb P) 0 X (Nat.zero_le _)
    (fun x _ hx => by rw [hEq x hx])
  have F1 := hEq 0 (by omega)
  simp only [zero_add] at F1
  simp only [Nat.sub_zero] at hG
  unfold pdUpper at hp
  have hZ : A P ^ X < 1 := pow_lt_one₀ ha0.le ha1 (by omega)
  have hZ0 : 0 ≤ A P ^ X := by positivity
  rw [le_div_iff₀ (by linarith), pow_succ] at hp
  generalize Eb P = E at *
  generalize A P = a at *
  generalize a ^ X = Z at *
  have hZa : 0 < 1 - Z * a := by nlinarith
  have K2 : (1 - a) * U 0 * (1 - Z * a) =
      (a * (P.v - p) + E) * (1 - Z) + Z * (1 - a) * (a * (P.v + P.k) + E) := by
    linear_combination hG + Z * (1 - a) * hEX
  have K3 : E * (1 - Z * a) ≤ (1 - a) * U 0 * (1 - Z * a) := by
    rw [K2]; nlinarith
  have K1 : E ≤ (1 - a) * U 0 := le_of_mul_le_mul_right K3 hZa
  have : a * U 0 ≤ a * (P.v - p + U 1) := by nlinarith
  exact le_of_mul_le_mul_left this ha0

/-- Reverse of the proofs of Lemmas 7 and 8 (purchase in state `0` against the low option),
for a threshold `1 ≤ τ ≤ X`. -/
lemma rev_b (P : Params) (hP : P.Standing) (hlam : 0 < P.lam) (hq : 0 < P.q) (p : ℝ) (X : ℕ)
    (τ : ℕ) (hτ1 : 1 ≤ τ) (hτX : τ ≤ X) (U : ℕ → ℝ)
    (hEqL : ∀ x < τ, U x = A P * (P.v - p) + Eb P + A P * U (x + 1))
    (hEqB : ∀ x, τ ≤ x → x < X → U x = A1 P * (P.v - p) + A1 P * U (x + 1))
    (hEX : U X = A1 P * (P.v + P.k) + A1 P * U 0) (hp : p ≤ pB P X τ) :
    U 0 ≤ P.v - p + U 1 := by
  obtain ⟨ha0, ha1, hb0, hb1, hR, hR2⟩ := basics P hP hlam hq
  have hG1 := geom U (A P) (A P * (P.v - p) + Eb P) 0 τ (Nat.zero_le _)
    (fun x _ hx => by rw [hEqL x hx])
  have hG2 := geom U (A1 P) (A1 P * (P.v - p)) τ X hτX
    (fun x h1 h2 => by rw [hEqB x h1 h2])
  have F1 := hEqL 0 (by omega)
  simp only [zero_add] at F1
  have F3 := hEX
  simp only [Nat.sub_zero] at hG1
  have hZa : A P ^ τ < 1 := pow_lt_one₀ ha0.le ha1 (by omega)
  have hZa0 : 0 < A P ^ τ := by positivity
  have hZb : A1 P ^ (X - τ) ≤ 1 := pow_le_one₀ hb0.le hb1.le
  have hZb0 : 0 < A1 P ^ (X - τ) := by positivity
  have hW : A P ^ τ = A P ^ (τ - 1) * A P := by
    rw [← pow_succ, Nat.sub_add_cancel hτ1]
  unfold pB at hp
  rw [show X - τ + 1 = (X - τ) + 1 by omega, pow_succ] at hp
  have hden : 0 < A P ^ τ * (1 - A1 P ^ (X - τ)) + P.q * (1 - A P ^ τ) := by
    have : 0 ≤ A P ^ τ * (1 - A1 P ^ (X - τ)) := mul_nonneg hZa0.le (by linarith)
    have : 0 < P.q * (1 - A P ^ τ) := mul_pos hq (by linarith)
    linarith
  rw [le_div_iff₀ hden] at hp
  generalize Eb P = E at *
  generalize A1 P = b at *
  generalize A P ^ (τ - 1) = Wa at *
  generalize A P ^ τ = Za at *
  generalize A P = a at *
  generalize b ^ (X - τ) = Zb at *
  generalize U 0 = u0 at *
  generalize U 1 = u1 at *
  generalize U X = uX at *
  generalize U τ = ut at *
  generalize P.q = q at *
  generalize P.v = v at *
  generalize P.vbar = vb at *
  generalize P.k = k at *
  have h1a : 0 < 1 - a := by linarith
  have h1b : 0 < 1 - b := by linarith
  have hkap : 0 < (b * (1 - a) * (1 - b)) := by positivity
  have hDt : 0 < (a * b * (1 - a) * (1 - b) * (1 - Za * Zb * b)) := by
    have : Za * Zb * b < 1 := by
      have e1 : Za * Zb ≤ Za := mul_le_of_le_one_right hZa0.le hZb
      have e2 : Za * Zb * b ≤ Za * Zb := mul_le_of_le_one_right (by positivity) hb1.le
      linarith
    have : 0 < 1 - Za * Zb * b := by linarith
    positivity
  have key : (b * (1 - a) * (1 - b)) * (b ^ 2 * (1 - a) ^ 2) * ((q * (1 - Za * (Zb * b)) * v + (1 - q) * Za * (1 - Zb * b) * (v - vb) + Za * Zb * (1 - b) * k) - p * (Za * (1 - Zb) + q * (1 - Za))) = (b * (1 - a) * (1 - b)) * (a * b * (1 - a) * (1 - b) * (1 - Za * Zb * b)) * (v - p + u1 - u0) := by
    linear_combination (-b^2*(a - 1)^2*(b - 1)^2) * hG1 + (-Za*b^2*(a - 1)^3*(b - 1)) * hG2 + (Za*Zb*b^2*(a - 1)^3*(b - 1)^2) * F3 + (-b^2*(a - 1)^2*(b - 1)^2*(Za*Zb*b - 1)) * F1 + (b^2*(a - 1)^2*(b - 1)*(-E*Zb*b^2 + E*Zb*b + E*b - E - Zb*a*b^2*q*vb + Zb*a*b^2*vb + Zb*b^2*q*vb - Zb*b^2*vb + a*b*p*q - a*b*p - a*b*q*v + a*b*q*vb + a*b*v - a*b*vb + a*p - a*v - b*p*q + b*q*v - b*q*vb + b*vb)) * hW + (Wa*a*b^2*(a - 1)^2*(b - 1)*(Zb*b - 1)) * hR2 + (b^2*(a - 1)^2*(b - 1)*(p - v)*(Wa*a - 1)) * hR
  have hT : 0 ≤ (b * (1 - a) * (1 - b)) * (b ^ 2 * (1 - a) ^ 2) * ((q * (1 - Za * (Zb * b)) * v + (1 - q) * Za * (1 - Zb * b) * (v - vb) + Za * Zb * (1 - b) * k) - p * (Za * (1 - Zb) + q * (1 - Za))) :=
    mul_nonneg (by positivity) (by linarith)
  rw [key] at hT
  have := (mul_nonneg_iff_of_pos_left (mul_pos hkap hDt)).1 hT
  linarith

/-- `p^D` is nondecreasing in its threshold. -/
lemma pD_step (P : Params) (hP : P.Standing) (hlam : 0 < P.lam) (hq : 0 < P.q) (X j : ℕ)
    (hj : j + 1 ≤ X) : pD P X j ≤ pD P X (j + 1) := by
  obtain ⟨ha0, ha1, hb0, hb1, hR, -⟩ := basics P hP hlam hq
  have hvv : 0 ≤ P.v - P.vbar + P.k := by
    have := hP.2.2.2.2.2.2.2.1; have := hP.2.2.2.2.2.2.2.2; linarith
  unfold pD
  rw [show X - j + 1 = (X - (j + 1)) + 2 by omega, show X - j = (X - (j + 1)) + 1 by omega,
    show X - (j + 1) + 1 = (X - (j + 1)) + 1 by omega, pow_add, pow_add, pow_succ (A P) j,
    pow_one]
  have hc0 : 0 < A1 P ^ (X - (j + 1)) := by positivity
  have hc1 : A1 P ^ (X - (j + 1)) ≤ 1 := pow_le_one₀ hb0.le hb1.le
  have hz0 : 0 < A P ^ j := by positivity
  have hz1 : A P ^ j ≤ 1 := pow_le_one₀ ha0.le ha1.le
  generalize A1 P = b at *
  generalize A P = a at *
  generalize b ^ (X - (j + 1)) = c at *
  generalize a ^ j = z at *
  generalize P.q = q at *
  generalize P.v = v at *
  generalize P.vbar = vb at *
  generalize P.k = k at *
  have hcb : c * b < 1 := by
    have := mul_le_of_le_one_left hb0.le hc1; linarith
  have hza : z * a ≤ 1 := by
    have := mul_le_of_le_one_left ha0.le hz1; linarith
  have hD1 : 0 < 1 - c * b + q * (1 - z) * (c * b ^ 2) := by
    have : 0 ≤ q * (1 - z) * (c * b ^ 2) := by
      have : 0 ≤ 1 - z := by linarith
      positivity
    linarith
  have hD2 : 0 < 1 - c + q * (1 - z * a) * (c * b) := by
    have : c < 1 ∨ c = 1 := lt_or_eq_of_le hc1
    have : 0 ≤ q * (1 - z * a) * (c * b) := by
      have : 0 ≤ 1 - z * a := by linarith
      positivity
    have : 0 < q * (1 - z * a) * (c * b) ∨ c < 1 := by
      rcases lt_or_eq_of_le hc1 with h | h
      · exact Or.inr h
      · left
        have : 0 < 1 - z * a := by
          have : z * a < 1 := by
            have := mul_lt_of_lt_one_right hz0 ha1; linarith
          linarith
        positivity
    rcases this with h | h <;> linarith
  rw [div_le_div_iff₀ hD1 hD2]
  have e : ((1 - c * b + q * (1 - z * a) * (c * b)) * (v - vb) + c * (1 - b) * k) *
      (1 - c * b + q * (1 - z) * (c * b ^ 2)) -
      ((1 - c * b ^ 2 + q * (1 - z) * (c * b ^ 2)) * (v - vb) + c * b * (1 - b) * k) *
      (1 - c + q * (1 - z * a) * (c * b)) =
      c * (1 - b) * (v - vb + k) * (1 - b) * (1 - c * b * z * a) := by
    linear_combination (b * c ^ 2 * z * (1 - b) * (k + v - vb)) * hR
  have : 0 ≤ c * (1 - b) * (v - vb + k) * (1 - b) * (1 - c * b * z * a) := by
    have : c * b * z * a ≤ 1 := by
      have h1 : c * b * (z * a) ≤ c * b := mul_le_of_le_one_right (by positivity) hza
      nlinarith
    have : 0 ≤ 1 - c * b * z * a := by linarith
    have : 0 ≤ 1 - b := by linarith
    positivity
  linarith

lemma pD_mono (P : Params) (hP : P.Standing) (hlam : 0 < P.lam) (hq : 0 < P.q) (X i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ X) : pD P X i ≤ pD P X j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (pD_step P hP hlam hq X j hj)

lemma bell_both (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (V : ℕ → ℝ) (x : ℕ) (hx : x ≤ X)
    (h : P.δ * V x = A1 P * (if x < X then P.v - p + P.δ * V (x + 1)
      else P.v + P.k + P.δ * V 0)) : V x ≤ bell P p X V x := by
  have hP' := hP
  obtain ⟨hl0, hl1, hq0, hq1, -⟩ := hP'
  have c1 : 0 ≤ P.lam * P.q := mul_nonneg hl0 hq0
  have c2 : 0 ≤ P.lam * (1 - P.q) := mul_nonneg hl0 (by linarith)
  unfold bell
  split_ifs at h ⊢ with hx'
  · conv_lhs => rw [of_both P hP _ _ h]
    have := mul_le_mul_of_nonneg_left (le_max_left (P.v - p + P.δ * V (x + 1)) (P.δ * V x)) c1
    have := mul_le_mul_of_nonneg_left
      (le_max_left (P.v - p + P.δ * V (x + 1)) (P.vbar + P.δ * V x)) c2
    linarith
  · have hxX : x = X ∨ x ≠ X := eq_or_ne x X
    have e := of_both P hP _ _ h
    rcases hxX with rfl | hne
    · conv_lhs => rw [e]
      have := mul_le_mul_of_nonneg_left (le_max_left (P.v + P.k + P.δ * V 0) (P.δ * V x)) c1
      have := mul_le_mul_of_nonneg_left
        (le_max_left (P.v + P.k + P.δ * V 0) (P.vbar + P.δ * V x)) c2
      linarith
    · exfalso; exact hne (by omega)

lemma bell_low (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (V : ℕ → ℝ) (x : ℕ) (hx : x ≤ X)
    (h : P.δ * V x = A P * (if x < X then P.v - p + P.δ * V (x + 1)
      else P.v + P.k + P.δ * V 0) + Eb P) : V x ≤ bell P p X V x := by
  have hP' := hP
  obtain ⟨hl0, hl1, hq0, hq1, -⟩ := hP'
  have c1 : 0 ≤ P.lam * P.q := mul_nonneg hl0 hq0
  have c2 : 0 ≤ P.lam * (1 - P.q) := mul_nonneg hl0 (by linarith)
  unfold bell
  split_ifs at h ⊢ with hx'
  · conv_lhs => rw [of_low P hP _ _ h]
    have := mul_le_mul_of_nonneg_left (le_max_left (P.v - p + P.δ * V (x + 1)) (P.δ * V x)) c1
    have := mul_le_mul_of_nonneg_left
      (le_max_right (P.v - p + P.δ * V (x + 1)) (P.vbar + P.δ * V x)) c2
    linarith
  · have hxX : x = X := by omega
    subst hxX
    conv_lhs => rw [of_low P hP _ _ h]
    have := mul_le_mul_of_nonneg_left (le_max_left (P.v + P.k + P.δ * V 0) (P.δ * V x)) c1
    have := mul_le_mul_of_nonneg_left
      (le_max_right (P.v + P.k + P.δ * V 0) (P.vbar + P.δ * V x)) c2
    linarith

/-- Under `p ≤ p^D(0)` the consumer buys in state `0` against the low option. -/
lemma bl0_a (P : Params) (hP : P.Standing) (hlam : 0 < P.lam) (hq : 0 < P.q) (p : ℝ) (X : ℕ)
    (hX : 1 ≤ X) (J : ℕ → ℝ) (hJ : IsValueFn P p X J) (hp : p ≤ pD P X 0) :
    BuysLow P p J 0 := by
  obtain ⟨ha0, ha1, hb0, hb1, -, -⟩ := basics P hP hlam hq
  have hd0 : 0 < P.δ := hP.2.2.2.2.1
  have hd1 : P.δ < 1 := hP.2.2.2.2.2.1
  obtain ⟨U, hU, hUX⟩ := exists_sol
    (fun x => if x < X then A1 P * (P.v - p) else A1 P * (P.v + P.k)) (fun _ => A1 P) X
    (fun _ => ⟨hb0.le, hb1⟩)
  have hEq : ∀ x < X, U x = A1 P * (P.v - p) + A1 P * U (x + 1) := by
    intro x hx; rw [hU x hx, if_pos hx]
  have hEX : U X = A1 P * (P.v + P.k) + A1 P * U 0 := by rw [hUX, if_neg (lt_irrefl X)]
  have hrev := rev_a P hP hlam hq p X hX U hEq hEX hp
  set V := fun x => U x / P.δ with hV
  have hUV : ∀ x, U x = P.δ * V x := fun x => by simp only [hV]; field_simp
  have hsub : ∀ x ≤ X, V x ≤ bell P p X V x := by
    intro x hx
    apply bell_both P hP p X V x hx
    split_ifs with h
    · rw [← hUV, ← hUV, hEq x h]; ring
    · have : x = X := by omega
      subst this; rw [← hUV, ← hUV, hEX]; ring
  rw [hUV, hUV] at hrev
  have e0 := of_both P hP _ _ (show P.δ * V 0 = A1 P * (P.v - p + P.δ * V 1) by
    rw [← hUV, ← hUV, hEq 0 (by omega)]; ring)
  have hvb0 : 0 ≤ P.vbar := hP.2.2.2.2.2.2.1
  have hl0 : 0 ≤ P.lam := hP.1
  have hq1 : P.q ≤ 1 := hP.2.2.2.1
  apply bl0_of_sub P hP p X hX J hJ V hsub _ (by linarith)
  have : P.lam * P.vbar ≤ P.lam * (P.v - p + P.δ * V 1 - P.δ * V 0) :=
    mul_le_mul_of_nonneg_left (by linarith) hl0
  have : P.lam * (1 - P.q) * P.vbar ≤ P.lam * P.vbar := by
    have := mul_nonneg (mul_nonneg hl0 hq.le) hvb0; nlinarith
  nlinarith

/-- Under `p ≤ p^B(τ)` (`1 ≤ τ ≤ X`) the consumer buys in state `0` against the low option. -/
lemma bl0_b (P : Params) (hP : P.Standing) (hlam : 0 < P.lam) (hq : 0 < P.q) (p : ℝ) (X : ℕ)
    (J : ℕ → ℝ) (hJ : IsValueFn P p X J) (τ : ℕ) (hτ1 : 1 ≤ τ) (hτX : τ ≤ X)
    (hp : p ≤ pB P X τ) : BuysLow P p J 0 := by
  have hX : 1 ≤ X := by omega
  obtain ⟨ha0, ha1, hb0, hb1, -, -⟩ := basics P hP hlam hq
  have hd0 : 0 < P.δ := hP.2.2.2.2.1
  obtain ⟨U, hU, hUX⟩ := exists_sol
    (fun x => if x < τ then A P * (P.v - p) + Eb P
      else if x < X then A1 P * (P.v - p) else A1 P * (P.v + P.k))
    (fun x => if x < τ then A P else A1 P) X
    (fun x => by split_ifs <;> constructor <;> linarith)
  have hEqL : ∀ x < τ, U x = A P * (P.v - p) + Eb P + A P * U (x + 1) := by
    intro x hx; rw [hU x (by omega), if_pos hx, if_pos hx]
  have hEqB : ∀ x, τ ≤ x → x < X → U x = A1 P * (P.v - p) + A1 P * U (x + 1) := by
    intro x h1 h2; rw [hU x h2, if_neg (by omega), if_pos h2, if_neg (by omega)]
  have hEX : U X = A1 P * (P.v + P.k) + A1 P * U 0 := by
    rw [hUX, if_neg (by omega), if_neg (lt_irrefl X), if_neg (by omega)]
  have hrev := rev_b P hP hlam hq p X τ hτ1 hτX U hEqL hEqB hEX hp
  set V := fun x => U x / P.δ with hV
  have hUV : ∀ x, U x = P.δ * V x := fun x => by simp only [hV]; field_simp
  have hsub : ∀ x ≤ X, V x ≤ bell P p X V x := by
    intro x hx
    by_cases h1 : x < τ
    · apply bell_low P hP p X V x hx
      rw [if_pos (by omega), ← hUV, ← hUV, hEqL x h1]; ring
    · apply bell_both P hP p X V x hx
      split_ifs with h
      · rw [← hUV, ← hUV, hEqB x (by omega) h]; ring
      · have : x = X := by omega
        subst this; rw [← hUV, ← hUV, hEX]; ring
  rw [hUV, hUV] at hrev
  have e0 := of_low P hP _ _ (show P.δ * V 0 = A P * (P.v - p + P.δ * V 1) + Eb P by
    rw [← hUV, ← hUV, hEqL 0 (by omega)]; ring)
  have hl0 : 0 ≤ P.lam := hP.1
  have hq1 : P.q ≤ 1 := hP.2.2.2.1
  apply bl0_of_sub P hP p X hX J hJ V hsub _ hrev
  have : P.lam * P.q * (P.δ * V 0) ≤ P.lam * P.q * (P.v - p + P.δ * V 1) :=
    mul_le_mul_of_nonneg_left hrev (mul_nonneg hl0 hq.le)
  nlinarith

/-- Under `p ≤ ((1 − A^{X+1})v + A^X(1 − A)k)/(1 − A^X)` the consumer buys in state `0` against
the low option. -/
lemma bl0_d (P : Params) (hP : P.Standing) (hlam : 0 < P.lam) (hq : 0 < P.q) (p : ℝ) (X : ℕ)
    (hX : 1 ≤ X) (J : ℕ → ℝ) (hJ : IsValueFn P p X J) (hp : p ≤ pdUpper P X) :
    BuysLow P p J 0 := by
  obtain ⟨ha0, ha1, hb0, hb1, -, -⟩ := basics P hP hlam hq
  have hd0 : 0 < P.δ := hP.2.2.2.2.1
  obtain ⟨U, hU, hUX⟩ := exists_sol
    (fun x => if x < X then A P * (P.v - p) + Eb P else A P * (P.v + P.k) + Eb P)
    (fun _ => A P) X (fun _ => ⟨ha0.le, ha1⟩)
  have hEq : ∀ x < X, U x = A P * (P.v - p) + Eb P + A P * U (x + 1) := by
    intro x hx; rw [hU x hx, if_pos hx]
  have hEX : U X = A P * (P.v + P.k) + Eb P + A P * U 0 := by rw [hUX, if_neg (lt_irrefl X)]
  have hrev := rev_d P hP hlam hq p X hX U hEq hEX hp
  set V := fun x => U x / P.δ with hV
  have hUV : ∀ x, U x = P.δ * V x := fun x => by simp only [hV]; field_simp
  have hsub : ∀ x ≤ X, V x ≤ bell P p X V x := by
    intro x hx
    apply bell_low P hP p X V x hx
    split_ifs with h
    · rw [← hUV, ← hUV, hEq x h]; ring
    · have : x = X := by omega
      subst this; rw [← hUV, ← hUV, hEX]; ring
  rw [hUV, hUV] at hrev
  have e0 := of_low P hP _ _ (show P.δ * V 0 = A P * (P.v - p + P.δ * V 1) + Eb P by
    rw [← hUV, ← hUV, hEq 0 (by omega)]; ring)
  have hl0 : 0 ≤ P.lam := hP.1
  apply bl0_of_sub P hP p X hX J hJ V hsub _ hrev
  have : P.lam * P.q * (P.δ * V 0) ≤ P.lam * P.q * (P.v - p + P.δ * V 1) :=
    mul_le_mul_of_nonneg_left hrev (mul_nonneg hl0 hq.le)
  nlinarith

end BuyXFree.Threshold.CvAux

open BuyXFree.Threshold BuyXFree.Threshold.CvAux in
theorem solution (P : Params) (hP : P.Standing) (hlam : 0 < P.lam) (hq : 0 < P.q)
    (p : ℝ) (X : ℕ) (hX : 1 ≤ X) (J : ℕ → ℝ) (hJ : IsValueFn P p X J) :
    -- (a)
    (p ≤ pD P X 0 →
      (∀ x < X, BuysHigh P p J x) ∧ RedeemsHigh P X J ∧
        (∀ x < X, BuysLow P p J x) ∧ RedeemsLow P X J) ∧
    -- (b)
    (∀ τ : ℕ, 1 ≤ τ → τ + 1 ≤ X → pD P X (τ - 1) < p → p ≤ min (pB P X τ) (pD P X τ) →
      (∀ x < X, (BuysHigh P p J x ↔ τ ≤ x)) ∧ RedeemsHigh P X J ∧
        (∀ x < X, BuysLow P p J x) ∧ RedeemsLow P X J) ∧
    -- (c)
    (pD P X (X - 1) < p → p ≤ min (pB P X X) (pD P X X) →
      (∀ x < X, ¬ BuysHigh P p J x) ∧ RedeemsHigh P X J ∧
        (∀ x < X, BuysLow P p J x) ∧ RedeemsLow P X J) ∧
    -- (d)
    (pD P X X < p → p ≤ pdUpper P X →
      (∀ x < X, ¬ BuysHigh P p J x) ∧ ¬ RedeemsHigh P X J ∧
        (∀ x < X, BuysLow P p J x) ∧ RedeemsLow P X J) := by
  have hP' := hP
  obtain ⟨hl0, hl1, hq0, hq1, hd0, hd1, hvb0, hvbv, hk0⟩ := hP'
  have hRL : RedeemsLow P X J := by
    have := lemma_4 P hP p X hX J hJ; unfold RedeemsLow; linarith
  have hBLall : BuysLow P p J 0 → ∀ x < X, BuysLow P p J x := by
    intro h0 x hx
    induction x with
    | zero => exact h0
    | succ n ih => exact (corollary_1 P hP p X hX J hJ n (by omega)).1 (ih (by omega))
  have hup : ∀ x, BuysHigh P p J x → ∀ n, x + n < X → BuysHigh P p J (x + n) := by
    intro x hb n
    induction n with
    | zero => intro _; exact hb
    | succ n ih =>
      intro hn
      exact (corollary_1 P hP p X hX J hJ (x + n) (by omega)).2 (ih (by omega))
  have hup' : ∀ x y, x ≤ y → y < X → BuysHigh P p J x → BuysHigh P p J y := by
    intro x y hxy hy hb
    have := hup x hb (y - x) (by omega)
    rwa [show x + (y - x) = y by omega] at this
  have hR5 : BuysHigh P p J (X - 1) → RedeemsHigh P X J := by
    intro h
    unfold BuysHigh at h
    rw [Nat.sub_add_cancel hX] at h
    have := lemma_5 P hP p X hX J hJ (by linarith)
    unfold RedeemsHigh; linarith
  -- classification of the behaviour against the high option
  have classify : BuysHigh P p J 0 ∨
      (∃ t, 1 ≤ t ∧ t + 1 ≤ X ∧ BuysHigh P p J t ∧ ¬ BuysHigh P p J (t - 1) ∧
        ∀ x < X, (BuysHigh P p J x ↔ t ≤ x)) ∨ (∀ x < X, ¬ BuysHigh P p J x) := by
    classical
    by_cases hex : ∃ x, x < X ∧ BuysHigh P p J x
    · have hs := Nat.find_spec hex
      by_cases h0 : Nat.find hex = 0
      · left; rw [h0] at hs; exact hs.2
      · right; left
        refine ⟨Nat.find hex, by omega, by omega, hs.2,
          fun h => Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega) ⟨by omega, h⟩,
          fun x hx => ⟨fun h => Nat.find_min' hex ⟨hx, h⟩, fun h => hup' _ x h hx hs.2⟩⟩
    · right; right
      intro x hx h; exact hex ⟨x, hx, h⟩
  have pm := pD_mono P hP hlam hq X
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (a)
    intro hp
    have hBL0 := bl0_a P hP hlam hq p X hX J hJ hp
    rcases classify with h0 | ⟨t, ht1, htX, htB, htn, -⟩ | hnone
    · have hall : ∀ x < X, BuysHigh P p J x := fun x hx => hup' 0 x (Nat.zero_le _) hx h0
      exact ⟨hall, hR5 (hall (X - 1) (by omega)), hBLall hBL0, hRL⟩
    · exfalso
      have := (converse_b P hP hlam hq p X J hJ t ht1 htX (hBL0) htB htn).2.2
      have := pm 0 (t - 1) (Nat.zero_le _) (by omega)
      linarith
    · exfalso
      by_cases hRH : RedeemsHigh P X J
      · have := (converse_c P hP hlam hq p X hX J hJ hBL0 (hnone (X - 1) (by omega)) hRH).2.1
        have := pm 0 (X - 1) (Nat.zero_le _) (by omega)
        linarith
      · have := (converse_d P hP hlam hq p X hX J hJ hBL0 hRH).2
        have := pm 0 X (Nat.zero_le _) le_rfl
        linarith
  · -- (b)
    intro τ hτ1 hτX hlo hhi
    have hBL0 := bl0_b P hP hlam hq p X J hJ τ hτ1 (by omega) (hhi.trans (min_le_left _ _))
    have hpD := hhi.trans (min_le_right _ _)
    rcases classify with h0 | ⟨t, ht1, htX, htB, htn, hiff⟩ | hnone
    · exfalso
      have := converse_a P hP hlam hq p X hX J hJ h0
      have := pm 0 (τ - 1) (Nat.zero_le _) (by omega)
      linarith
    · have hcb := converse_b P hP hlam hq p X J hJ t ht1 htX hBL0 htB htn
      have htτ : t = τ := by
        rcases lt_trichotomy t τ with h | h | h
        · exfalso
          have := pm t (τ - 1) (by omega) (by omega)
          linarith [hcb.2.1]
        · exact h
        · exfalso
          have := pm τ (t - 1) (by omega) (by omega)
          linarith [hcb.2.2]
      subst htτ
      exact ⟨hiff, hR5 ((hiff (X - 1) (by omega)).2 (by omega)), hBLall hBL0, hRL⟩
    · exfalso
      by_cases hRH : RedeemsHigh P X J
      · have := (converse_c P hP hlam hq p X hX J hJ hBL0 (hnone (X - 1) (by omega)) hRH).2.1
        have := pm τ (X - 1) (by omega) (by omega)
        linarith
      · have := (converse_d P hP hlam hq p X hX J hJ hBL0 hRH).2
        have := pm τ X (by omega) le_rfl
        linarith
  · -- (c)
    intro hlo hhi
    have hBL0 := bl0_b P hP hlam hq p X J hJ X hX le_rfl (hhi.trans (min_le_left _ _))
    have hpD := hhi.trans (min_le_right _ _)
    rcases classify with h0 | ⟨t, ht1, htX, htB, htn, -⟩ | hnone
    · exfalso
      have := converse_a P hP hlam hq p X hX J hJ h0
      have := pm 0 (X - 1) (Nat.zero_le _) (by omega)
      linarith
    · exfalso
      have := (converse_b P hP hlam hq p X J hJ t ht1 htX hBL0 htB htn).2.1
      have := pm t (X - 1) (by omega) (by omega)
      linarith
    · by_cases hRH : RedeemsHigh P X J
      · exact ⟨hnone, hRH, hBLall hBL0, hRL⟩
      · exfalso
        have := (converse_d P hP hlam hq p X hX J hJ hBL0 hRH).2
        linarith
  · -- (d)
    intro hlo hhi
    have hBL0 := bl0_d P hP hlam hq p X hX J hJ hhi
    rcases classify with h0 | ⟨t, ht1, htX, htB, htn, -⟩ | hnone
    · exfalso
      have := converse_a P hP hlam hq p X hX J hJ h0
      have := pm 0 X (Nat.zero_le _) le_rfl
      linarith
    · exfalso
      have := (converse_b P hP hlam hq p X J hJ t ht1 htX hBL0 htB htn).2.1
      have := pm t X (by omega) le_rfl
      linarith
    · by_cases hRH : RedeemsHigh P X J
      · exfalso
        have := (converse_c P hP hlam hq p X hX J hJ hBL0 (hnone (X - 1) (by omega)) hRH).2.2
        linarith
      · exact ⟨hnone, hRH, hBLall hBL0, hRL⟩
