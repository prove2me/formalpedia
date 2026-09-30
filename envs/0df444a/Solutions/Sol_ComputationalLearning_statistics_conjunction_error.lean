-- Prove2me | solution 1 for ComputationalLearning.statistics_conjunction_error
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T03:26:20.451726+00:00
-- url     : https://prove2.me/submissions/61b2536a-fdd5-417c-a094-e8bf7504c820

import Mathlib
import Definitions.Def_ComputationalLearning_Noise

open MeasureTheory ProbabilityTheory

namespace ComputationalLearning

theorem stat_main {n : ℕ} (T : Conjunction (Fin n)) (D : Measure (Cube (Fin n)))
    [IsProbabilityMeasure D] {ε : ℝ} (hε : 0 < ε) :
    errorOf D (evalConj T) (evalConj (statisticsConj D (evalConj T) ε)) ≤ ε / 2 := by
  classical
  set c := evalConj T with hc
  set E := statisticsConj D c ε with hE
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hempty : ∀ U : Conjunction (Fin 0), U = ∅ :=
      fun U => Finset.eq_empty_of_forall_notMem (fun l _ => l.1.elim0)
    have h0 : {a : Cube (Fin 0) | evalConj E a ≠ c a} = ∅ := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      rw [hc, hempty E, hempty T]
    unfold errorOf
    rw [h0]
    simp only [measure_empty, ENNReal.toReal_zero]
    linarith
  set q := ε / (8 * (n : ℝ)) with hq
  have hn : (0:ℝ) < n := by exact_mod_cast hnpos
  have hqpos : 0 < q := by positivity
  set FN := ⋃ l ∈ E, {a : Cube (Fin n) | a l.1 ≠ l.2 ∧ c a = true} with hFN
  set T' := T.filter (fun l => zeroProb D l < q) with hT'
  set FP := ⋃ l ∈ T', {a : Cube (Fin n) | a l.1 ≠ l.2} with hFP
  have hsub : {a | evalConj E a ≠ c a} ⊆ FN ∪ FP := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha
    cases hca : c a
    · have hEa : evalConj E a = true := by
        cases h : evalConj E a
        · exact absurd (h.trans hca.symm) ha
        · rfl
      right
      have hnot : ¬ ∀ l ∈ T, a l.1 = l.2 := by
        intro hall
        have hct : c a = true := by
          simp only [hc, evalConj, decide_eq_true_eq]; exact hall
        rw [hca] at hct; exact Bool.false_ne_true hct
      push Not at hnot
      obtain ⟨l, hlT, hla⟩ := hnot
      rw [Set.mem_iUnion₂]
      refine ⟨l, Finset.mem_filter.mpr ⟨hlT, ?_⟩, hla⟩
      by_contra hge
      push Not at hge
      have hpos0 : zeroPosProb D c l = 0 := by
        unfold zeroPosProb
        have hemp : {b : Cube (Fin n) | b l.1 ≠ l.2 ∧ c b = true} = ∅ := by
          ext b
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
          intro hb hcb
          simp only [hc, evalConj, decide_eq_true_eq] at hcb
          exact hb (hcb l hlT)
        rw [hemp]; simp
      have hlE : l ∈ E := by
        simp only [hE, statisticsConj, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hge, by rw [hpos0]; exact hqpos⟩
      simp only [evalConj, decide_eq_true_eq] at hEa
      exact hla (hEa l hlE)
    · have hEa : evalConj E a = false := by
        cases h : evalConj E a
        · rfl
        · exact absurd (h.trans hca.symm) ha
      left
      simp only [evalConj, decide_eq_false_iff_not] at hEa
      push Not at hEa
      obtain ⟨l, hlE, hla⟩ := hEa
      rw [Set.mem_iUnion₂]
      exact ⟨l, hlE, hla, hca⟩
  have hcardlit : ∀ s : Finset (Fin n × Bool), (s.card : ℝ) ≤ 2 * n := by
    intro s
    have : s.card ≤ 2 * n := by
      calc s.card ≤ (Finset.univ : Finset (Fin n × Bool)).card := Finset.card_le_univ _
        _ = 2 * n := by simp [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring
    exact_mod_cast this
  have h2nq : 2 * (n : ℝ) * q = ε / 4 := by rw [hq]; field_simp; ring
  have hFNb : D.real FN ≤ ε / 4 := by
    calc D.real FN ≤ ∑ l ∈ E, D.real {a : Cube (Fin n) | a l.1 ≠ l.2 ∧ c a = true} :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ l ∈ E, q := Finset.sum_le_sum fun l hl => by
          have := (Finset.mem_filter.mp hl).2.2
          exact this.le
      _ = E.card * q := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * n * q := mul_le_mul_of_nonneg_right (hcardlit E) hqpos.le
      _ = ε / 4 := h2nq
  have hFPb : D.real FP ≤ ε / 4 := by
    calc D.real FP ≤ ∑ l ∈ T', D.real {a : Cube (Fin n) | a l.1 ≠ l.2} :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ l ∈ T', q := Finset.sum_le_sum fun l hl => by
          have := (Finset.mem_filter.mp hl).2
          exact this.le
      _ = T'.card * q := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * n * q := mul_le_mul_of_nonneg_right (hcardlit T') hqpos.le
      _ = ε / 4 := h2nq
  unfold errorOf
  calc (D {a | evalConj E a ≠ c a}).toReal ≤ D.real (FN ∪ FP) := measureReal_mono hsub
    _ ≤ D.real FN + D.real FP := measureReal_union_le _ _
    _ ≤ ε / 4 + ε / 4 := add_le_add hFNb hFPb
    _ = ε / 2 := by ring

end ComputationalLearning

open ComputationalLearning

theorem solution {n : ℕ} (T : Conjunction (Fin n)) (D : Measure (Cube (Fin n)))
    [IsProbabilityMeasure D] {ε : ℝ} (hε : 0 < ε) :
    errorOf D (evalConj T) (evalConj (statisticsConj D (evalConj T) ε)) ≤ ε / 2 := by
  exact stat_main T D hε
