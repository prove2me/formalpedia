-- Prove2me | solution 1 for ExpBias.OwnBias.proposition_1_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:55:43.243869+00:00
-- url     : https://prove2.me/submissions/9c931887-705f-4f55-b314-ed286a2e8ee3

import Mathlib
import Definitions.Def_ExpBias_OwnBias_Model
open ExpBias.OwnBias

theorem solution(P : Params) (hP : P.Standing) :
    (pHat P < P.p → value P (nBiased P) < value P (wBiased P)) ∧
    (P.p < pHat P → value P (wBiased P) < value P (nBiased P)) := by
  obtain ⟨h1, h2, hp0, hp1, hL1, hL2⟩ := hP
  have hl0 : 0 < lam P := by unfold lam; linarith
  have hl1 : lam P < 1 := by unfold lam; linarith
  have hb : 0 < P.vW - P.vN := by linarith
  have rv : ∀ e : Experiment, ∀ d : Bool → Bool, ruleValue P e d =
      P.p * (e.lw * payoff P true (d true) + (1 - e.lw) * payoff P true (d false)) +
      (1 - P.p) * ((1 - e.ln) * payoff P false (d true) + e.ln * payoff P false (d false)) := by
    intro e d
    simp [ruleValue, joint, Fintype.sum_bool]
    ring
  have key : ∀ e e' : Experiment, (∀ d, ruleValue P e d < ruleValue P e' id) →
      value P e < value P e' := by
    intro e e' H
    unfold value
    exact lt_of_lt_of_le ((Finset.sup'_lt_iff (H := Finset.univ_nonempty)).2 (fun d _ => H d))
      (Finset.le_sup' (ruleValue P e') (Finset.mem_univ id))
  have H1 : 0 < (1 - P.p) * lam P * (P.vS - P.vN) :=
    mul_pos (mul_pos (by linarith) hl0) (by linarith)
  have H3 : 0 < P.p * lam P * (P.vW - P.vS) := mul_pos (mul_pos hp0 hl0) (by linarith)
  constructor
  · intro h
    rw [pHat, div_lt_iff₀ hb] at h
    have hA : 0 < P.p * P.vW + (1 - P.p) * P.vN - P.vS := by nlinarith
    have H2 : 0 < (1 - lam P) * (P.p * P.vW + (1 - P.p) * P.vN - P.vS) :=
      mul_pos (by linarith) hA
    apply key
    intro d
    rw [rv, rv]
    rcases hdt : d true <;> rcases hdf : d false <;>
      simp only [hdt, hdf, payoff, wBiased, nBiased, id, ↓reduceIte, Bool.false_eq_true] <;>
      nlinarith
  · intro h
    rw [pHat, lt_div_iff₀ hb] at h
    have hB : 0 < P.vS - P.p * P.vW - (1 - P.p) * P.vN := by nlinarith
    have H4 : 0 < (1 - lam P) * (P.vS - P.p * P.vW - (1 - P.p) * P.vN) :=
      mul_pos (by linarith) hB
    apply key
    intro d
    rw [rv, rv]
    rcases hdt : d true <;> rcases hdf : d false <;>
      simp only [hdt, hdf, payoff, wBiased, nBiased, id, ↓reduceIte, Bool.false_eq_true] <;>
      nlinarith
