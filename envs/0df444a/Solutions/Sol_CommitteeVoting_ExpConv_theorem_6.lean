-- Prove2me | solution 1 for CommitteeVoting.ExpConv.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T19:46:23.032034+00:00
-- url     : https://prove2.me/submissions/f4b1aeae-c206-4918-917b-5f78453b93cb

import Mathlib

open MeasureTheory ProbabilityTheory

namespace CVEC6

lemma hoeffUnit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (Z : Fin n → Ω → ℝ) (hZm : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (a : ℝ) (hab : ∀ i, ∀ᵐ ω ∂P, Z i ω ∈ Set.Icc a (a + 1)) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ ∑ i, (Z i ω - ∫ x, Z i x ∂P)} ≤ Real.exp (-(2 * ε ^ 2 / n)) := by
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      HasSubgaussianMGF (fun ω => Z i ω - ∫ x, Z i x ∂P) ((‖(a + 1) - a‖₊ / 2) ^ 2) P := by
    intro i _
    exact hasSubgaussianMGF_of_mem_Icc (hZm i).aemeasurable (hab i)
  have hind' : iIndepFun (fun i ω => Z i ω - ∫ x, Z i x ∂P) P :=
    hind.comp (fun i x => x - ∫ y, Z i y ∂P) (fun i => by fun_prop)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind' hsub hε
  refine h.trans (le_of_eq ?_)
  congr 1
  have : ((∑ _i : Fin n, ((‖(a + 1) - a‖₊ / 2) ^ 2 : NNReal) : NNReal) : ℝ) = n / 4 := by
    push_cast
    simp [Finset.sum_const, Finset.card_univ]
    ring
  rw [this]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have : (n:ℝ) ≠ 0 := by positivity
    field_simp
    ring

end CVEC6

open CVEC6

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 1 ≤ n) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (h01 : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (q : Fin n → ℝ) (hq : ∀ i, P.real {ω | X i ω = 1} = q i) {t : ℝ} (ht : 0 < t) :
    P.real {ω | ∑ i, q i + t < ∑ i, X i ω} ≤ Real.exp (-(2 * t ^ 2 / n)) ∧
      P.real {ω | ∑ i, X i ω < ∑ i, q i - t} ≤ Real.exp (-(2 * t ^ 2 / n)) := by
  have hint : ∀ i, ∫ x, X i x ∂P = q i := by
    intro i
    have hs : MeasurableSet {ω | X i ω = 1} := measurableSet_eq_fun (hXm i) measurable_const
    have hae : X i =ᵐ[P] Set.indicator {ω | X i ω = 1} (fun _ => (1:ℝ)) := by
      filter_upwards [h01 i] with ω hω
      rcases hω with h | h <;> simp [Set.indicator, h]
    rw [integral_congr_ae hae, integral_indicator hs, ← hq i]
    simp
  have hIcc : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc (0:ℝ) (0 + 1) := by
    intro i
    filter_upwards [h01 i] with ω hω
    rcases hω with h | h <;> simp [h]
  have hIccN : ∀ i, ∀ᵐ ω ∂P, (fun ω => -X i ω) ω ∈ Set.Icc (-1:ℝ) (-1 + 1) := by
    intro i
    filter_upwards [h01 i] with ω hω
    rcases hω with h | h <;> simp [h]
  constructor
  · have hA := hoeffUnit P X hXm hind 0 hIcc ht.le
    refine (measureReal_mono ?_).trans hA
    intro ω hω
    simp only [Set.mem_setOf_eq, hint, Finset.sum_sub_distrib] at hω ⊢
    linarith
  · have hindN : iIndepFun (fun i ω => -X i ω) P :=
      hind.comp (fun _ x => -x) (fun _ => by fun_prop)
    have hB := hoeffUnit P (fun i ω => -X i ω) (fun i => (hXm i).neg) hindN (-1) hIccN ht.le
    refine (measureReal_mono ?_).trans hB
    intro ω hω
    simp only [Set.mem_setOf_eq, integral_neg, hint, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib] at hω ⊢
    linarith
