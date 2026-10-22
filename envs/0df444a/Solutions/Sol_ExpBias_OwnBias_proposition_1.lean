-- Prove2me | solution 1 for ExpBias.OwnBias.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T10:56:12.915205+00:00
-- url     : https://prove2.me/submissions/724aa331-2312-4dfd-8401-80666b1cc348

import Mathlib
import Definitions.Def_ExpBias_OwnBias_Model

set_option autoImplicit false

namespace ExpBias.OwnBias

/-- Normalised rule value (minus the status-quo payoff). -/
def p1aux_F (A B lw ln : ℝ) (b1 b2 : Bool) : ℝ :=
  (if b1 then A * lw - B * (1 - ln) else 0) + (if b2 then A * (1 - lw) - B * ln else 0)

lemma p1aux_ruleValue_eq (P : Params) (e : Experiment) (d : Bool → Bool) :
    ruleValue P e d = P.vS +
      p1aux_F (P.p * (P.vW - P.vS)) ((1 - P.p) * (P.vS - P.vN)) e.lw e.ln (d true) (d false) := by
  unfold ruleValue joint payoff p1aux_F
  simp only [Fintype.sum_bool]
  rcases Bool.eq_false_or_eq_true (d true) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (d false) with h2 | h2 <;>
    simp [h1, h2] <;> ring

lemma p1aux_le_value (P : Params) (e : Experiment) (d : Bool → Bool) :
    ruleValue P e d ≤ value P e :=
  Finset.le_sup' (ruleValue P e) (Finset.mem_univ d)

lemma p1aux_value_le (P : Params) (e : Experiment) (c : ℝ) (h : ∀ d, ruleValue P e d ≤ c) :
    value P e ≤ c :=
  Finset.sup'_le _ _ (fun d _ => h d)

lemma p1aux_exists_rule (P : Params) (e : Experiment) : ∃ d, value P e = ruleValue P e d := by
  obtain ⟨d, _, h⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (ruleValue P e)
  exact ⟨d, h⟩

lemma p1aux_bound1 (A B lw ln L : ℝ) (hAB : B < A) (hB : 0 < B)
    (h1 : 0 < lw) (h2 : lw ≤ 1) (h3 : 0 < ln) (h4 : ln ≤ 1) (h5 : 1 < lw + ln) (h6 : lw + ln ≤ L)
    (b1 b2 : Bool) : p1aux_F A B lw ln b1 b2 ≤ A - B + B * (L - 1) := by
  have hL : 1 < L := by linarith
  have k1 : 0 ≤ B * (L - lw - ln) := mul_nonneg hB.le (by linarith)
  have k2 : 0 ≤ (A - B) * (1 - lw) := mul_nonneg (by linarith) (by linarith)
  have k3 : 0 < (A - B) * lw := mul_pos (by linarith) h1
  have k4 : 0 < B * (lw + ln - 1) := mul_pos hB (by linarith)
  have k5 : 0 < B * (L - 1) := mul_pos hB (by linarith)
  unfold p1aux_F
  cases b1 <;> cases b2 <;> simp <;> nlinarith

lemma p1aux_eq1 (A B lw ln L : ℝ) (hAB : B < A) (hB : 0 < B)
    (h1 : 0 < lw) (h2 : lw ≤ 1) (h3 : 0 < ln) (h4 : ln ≤ 1) (h5 : 1 < lw + ln) (h6 : lw + ln ≤ L)
    (b1 b2 : Bool) (h : A - B + B * (L - 1) ≤ p1aux_F A B lw ln b1 b2) : lw = 1 ∧ ln = L - 1 := by
  have hL : 1 < L := by linarith
  have k1 : 0 ≤ B * (L - lw - ln) := mul_nonneg hB.le (by linarith)
  have k3 : 0 < (A - B) * lw := mul_pos (by linarith) h1
  have k4 : 0 < B * (lw + ln - 1) := mul_pos hB (by linarith)
  have k5 : 0 < B * (L - 1) := mul_pos hB (by linarith)
  unfold p1aux_F at h
  cases b1 <;> cases b2 <;> simp at h
  · nlinarith
  · nlinarith
  · have k6 : (A - B) * (1 - lw) ≤ 0 := by nlinarith
    have hlw : lw = 1 := by
      by_contra hne
      have : 0 < (A - B) * (1 - lw) :=
        mul_pos (by linarith) (by rcases lt_or_eq_of_le h2 with h' | h' <;> [linarith; exact absurd h' hne])
      linarith
    subst hlw
    have : B * (L - 1) ≤ B * ln := by nlinarith
    have : L - 1 ≤ ln := le_of_mul_le_mul_left this hB
    exact ⟨rfl, by linarith⟩
  · nlinarith

lemma p1aux_bound2 (A B lw ln L : ℝ) (hAB : A < B) (hA : 0 < A)
    (h1 : 0 < lw) (h2 : lw ≤ 1) (h3 : 0 < ln) (h4 : ln ≤ 1) (h5 : 1 < lw + ln) (h6 : lw + ln ≤ L)
    (b1 b2 : Bool) : p1aux_F A B lw ln b1 b2 ≤ A * (L - 1) := by
  have hL : 1 < L := by linarith
  have hB : 0 < B := by linarith
  have k1 : 0 ≤ A * (L - lw - ln) := mul_nonneg hA.le (by linarith)
  have k2 : 0 ≤ (B - A) * (1 - ln) := mul_nonneg (by linarith) (by linarith)
  have k3 : 0 ≤ (B - A) * (1 - lw) := mul_nonneg (by linarith) (by linarith)
  have k4 : 0 < B * (lw + ln - 1) := mul_pos hB (by linarith)
  have k5 : 0 < A * (L - 1) := mul_pos hA (by linarith)
  unfold p1aux_F
  cases b1 <;> cases b2 <;> simp <;> nlinarith

lemma p1aux_eq2 (A B lw ln L : ℝ) (hAB : A < B) (hA : 0 < A)
    (h1 : 0 < lw) (h2 : lw ≤ 1) (h3 : 0 < ln) (h4 : ln ≤ 1) (h5 : 1 < lw + ln) (h6 : lw + ln ≤ L)
    (b1 b2 : Bool) (h : A * (L - 1) ≤ p1aux_F A B lw ln b1 b2) : lw = L - 1 ∧ ln = 1 := by
  have hL : 1 < L := by linarith
  have hB : 0 < B := by linarith
  have k1 : 0 ≤ A * (L - lw - ln) := mul_nonneg hA.le (by linarith)
  have k3 : 0 ≤ (B - A) * (1 - lw) := mul_nonneg (by linarith) (by linarith)
  have k4 : 0 < B * (lw + ln - 1) := mul_pos hB (by linarith)
  have k5 : 0 < A * (L - 1) := mul_pos hA (by linarith)
  unfold p1aux_F at h
  cases b1 <;> cases b2 <;> simp at h
  · nlinarith
  · nlinarith
  · have k6 : (B - A) * (1 - ln) ≤ 0 := by nlinarith
    have hln : ln = 1 := by
      by_contra hne
      have : 0 < (B - A) * (1 - ln) :=
        mul_pos (by linarith) (by rcases lt_or_eq_of_le h4 with h' | h' <;> [linarith; exact absurd h' hne])
      linarith
    subst hln
    have : A * (L - 1) ≤ A * lw := by nlinarith
    have : L - 1 ≤ lw := le_of_mul_le_mul_left this hA
    exact ⟨by linarith, rfl⟩
  · nlinarith

end ExpBias.OwnBias

open ExpBias.OwnBias in
theorem solution (P : ExpBias.OwnBias.Params) (hP : P.Standing) :
    (ExpBias.OwnBias.pHat P < P.p → ∀ e : ExpBias.OwnBias.Experiment,
      ExpBias.OwnBias.IsOptimal P e ↔ e = ExpBias.OwnBias.wBiased P) ∧
    (P.p < ExpBias.OwnBias.pHat P → ∀ e : ExpBias.OwnBias.Experiment,
      ExpBias.OwnBias.IsOptimal P e ↔ e = ExpBias.OwnBias.nBiased P) := by
  obtain ⟨hNS, hSW, hp0, hp1, hL1, hL2⟩ := hP
  set A := P.p * (P.vW - P.vS) with hAdef
  set B := (1 - P.p) * (P.vS - P.vN) with hBdef
  have hA : 0 < A := mul_pos hp0 (by linarith)
  have hB : 0 < B := mul_pos (by linarith) (by linarith)
  have hWN : 0 < P.vW - P.vN := by linarith
  have hpH : pHat P = (P.vS - P.vN) / (P.vW - P.vN) := rfl
  have hlam : lam P = P.Lam - 1 := rfl
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · rw [hpH, div_lt_iff₀ hWN] at hp
    have hAB : B < A := by rw [hAdef, hBdef]; nlinarith
    have hInW : InE P (wBiased P) := by
      unfold InE wBiased; simp only [hlam]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
    have hT : P.vS + (A - B + B * (P.Lam - 1)) ≤ value P (wBiased P) := by
      have := p1aux_le_value P (wBiased P) id
      rw [p1aux_ruleValue_eq, ← hAdef, ← hBdef] at this
      simp only [wBiased, hlam, p1aux_F, id] at this
      simp at this
      have e0 : value P (wBiased P) = value P ⟨1, P.Lam - 1⟩ := rfl
      rw [e0]
      nlinarith
    have hUB : ∀ e', InE P e' → value P e' ≤ P.vS + (A - B + B * (P.Lam - 1)) := by
      intro e' he'
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := he'
      apply p1aux_value_le
      intro d
      rw [p1aux_ruleValue_eq, ← hAdef, ← hBdef]
      have := p1aux_bound1 A B e'.lw e'.ln P.Lam hAB hB g1 g2 g3 g4 g5 g6 (d true) (d false)
      linarith
    intro e
    constructor
    · rintro ⟨he, hopt⟩
      have hv := hopt (wBiased P) hInW
      obtain ⟨d, hd⟩ := p1aux_exists_rule P e
      rw [hd, p1aux_ruleValue_eq, ← hAdef, ← hBdef] at hv
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := he
      have := p1aux_eq1 A B e.lw e.ln P.Lam hAB hB g1 g2 g3 g4 g5 g6 (d true) (d false) (by linarith)
      obtain ⟨lw, ln⟩ := e
      simp only at this
      simp only [wBiased, hlam, Experiment.mk.injEq]
      exact this
    · rintro rfl
      exact ⟨hInW, fun e' he' => (hUB e' he').trans hT⟩
  · rw [hpH, lt_div_iff₀ hWN] at hp
    have hAB : A < B := by rw [hAdef, hBdef]; nlinarith
    have hInN : InE P (nBiased P) := by
      unfold InE nBiased; simp only [hlam]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
    have hT : P.vS + A * (P.Lam - 1) ≤ value P (nBiased P) := by
      have := p1aux_le_value P (nBiased P) id
      rw [p1aux_ruleValue_eq, ← hAdef, ← hBdef] at this
      simp only [nBiased, hlam, p1aux_F, id] at this
      simp at this
      have e0 : value P (nBiased P) = value P ⟨P.Lam - 1, 1⟩ := rfl
      rw [e0]
      nlinarith
    have hUB : ∀ e', InE P e' → value P e' ≤ P.vS + A * (P.Lam - 1) := by
      intro e' he'
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := he'
      apply p1aux_value_le
      intro d
      rw [p1aux_ruleValue_eq, ← hAdef, ← hBdef]
      have := p1aux_bound2 A B e'.lw e'.ln P.Lam hAB hA g1 g2 g3 g4 g5 g6 (d true) (d false)
      linarith
    intro e
    constructor
    · rintro ⟨he, hopt⟩
      have hv := hopt (nBiased P) hInN
      obtain ⟨d, hd⟩ := p1aux_exists_rule P e
      rw [hd, p1aux_ruleValue_eq, ← hAdef, ← hBdef] at hv
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := he
      have := p1aux_eq2 A B e.lw e.ln P.Lam hAB hA g1 g2 g3 g4 g5 g6 (d true) (d false) (by linarith)
      obtain ⟨lw, ln⟩ := e
      simp only at this
      simp only [nBiased, hlam, Experiment.mk.injEq]
      exact this
    · rintro rfl
      exact ⟨hInN, fun e' he' => (hUB e' he').trans hT⟩
