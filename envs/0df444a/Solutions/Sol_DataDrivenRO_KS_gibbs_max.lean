-- Prove2me | solution 1 for DataDrivenRO.KS.gibbs_max
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:34:21.427645+00:00
-- url     : https://prove2.me/submissions/2680291b-03a1-4f29-8c27-726df7548fe4

import Mathlib
import Definitions.Def_DataDrivenRO_KS_Setting

open MeasureTheory

namespace GibbsMaxAux9f

lemma term_le (c pj qj Z : ℝ) (hp : 0 ≤ pj) (hq : 0 ≤ qj) (hZ : 0 < Z)
    (habs : 0 < qj → 0 < pj) :
    c * qj - qj * Real.log (qj / pj) - qj * Real.log Z ≤ pj * Real.exp c / Z - qj := by
  rcases hq.eq_or_lt with h | h
  · subst h
    simp only [zero_mul, mul_zero, sub_zero, zero_div, Real.log_zero]
    positivity
  · have hpj : 0 < pj := habs h
    set a : ℝ := pj * Real.exp c / (Z * qj) with ha
    have ha0 : 0 < a := by positivity
    have hlog : Real.log a = Real.log pj + c - Real.log Z - Real.log qj := by
      rw [ha, Real.log_div (by positivity) (by positivity),
        Real.log_mul hpj.ne' (Real.exp_pos c).ne', Real.log_mul hZ.ne' h.ne', Real.log_exp]
      ring
    have hdiv : Real.log (qj / pj) = Real.log qj - Real.log pj :=
      Real.log_div h.ne' hpj.ne'
    have key := Real.log_le_sub_one_of_pos ha0
    have h1 : qj * Real.log a ≤ qj * (a - 1) := mul_le_mul_of_nonneg_left key h.le
    have h2 : qj * a = pj * Real.exp c / Z := by
      rw [ha]; field_simp
    rw [hdiv]
    rw [hlog] at h1
    nlinarith [h1, h2]

lemma term_eq (c pj Z : ℝ) (hp : 0 ≤ pj) (hZ : 0 < Z) :
    c * (pj * Real.exp c / Z) - (pj * Real.exp c / Z) * Real.log ((pj * Real.exp c / Z) / pj)
      = (pj * Real.exp c / Z) * Real.log Z := by
  rcases hp.eq_or_lt with h | h
  · subst h; simp
  · have : (pj * Real.exp c / Z) / pj = Real.exp c / Z := by
      field_simp
    rw [this, Real.log_div (Real.exp_pos c).ne' hZ.ne', Real.log_exp]
    ring

end GibbsMaxAux9f

open DataDrivenRO.KS in
theorem solution {n : ℕ} (c p : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) :
    IsGreatest
      {s | ∃ q ∈ stdSimplex ℝ (Fin n), AbsCont q p ∧
        s = ∑ j, c j * q j - relEntropy q p}
      (Real.log (∑ j, p j * Real.exp (c j))) := by
  obtain ⟨hp0, hp1⟩ := hp
  set Z : ℝ := ∑ j, p j * Real.exp (c j) with hZdef
  have hZ : 0 < Z := by
    have hne : ∃ j, 0 < p j := by
      by_contra hcon
      push_neg at hcon
      have : ∑ j, p j = 0 :=
        Finset.sum_eq_zero (fun j _ => le_antisymm (hcon j) (hp0 j))
      rw [hp1] at this; exact one_ne_zero this
    obtain ⟨j, hj⟩ := hne
    calc 0 < p j * Real.exp (c j) := by positivity
      _ ≤ Z := Finset.single_le_sum (f := fun j => p j * Real.exp (c j))
            (fun i _ => mul_nonneg (hp0 i) (Real.exp_pos _).le) (Finset.mem_univ j)
  constructor
  · refine ⟨fun j => p j * Real.exp (c j) / Z, ⟨fun j => by have := hp0 j; positivity, ?_⟩, ?_, ?_⟩
    · rw [← Finset.sum_div, ← hZdef, div_self hZ.ne']
    · intro j hj
      rcases (hp0 j).eq_or_lt with h | h
      · simp [← h] at hj
      · exact h
    · unfold relEntropy
      rw [← Finset.sum_sub_distrib]
      simp only [GibbsMaxAux9f.term_eq (c _) (p _) Z (hp0 _) hZ]
      rw [← Finset.sum_mul, ← Finset.sum_div, ← hZdef, div_self hZ.ne', one_mul]
  · rintro s ⟨q, ⟨hq0, hq1⟩, habs, rfl⟩
    unfold relEntropy
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      GibbsMaxAux9f.term_le (c j) (p j) (q j) Z (hp0 j) (hq0 j) hZ (habs j))
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hq1, ← Finset.sum_div, ← hZdef, div_self hZ.ne'] at hsum
    linarith
