-- Prove2me | solution 1 for AvramDividend.Classical.chat06_selected_residual_survival_of_countwise_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:14:05.806801+00:00
-- url     : https://prove2.me/submissions/84d53ee9-8890-4311-ba11-c9f2e8a09b2e

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace AvramChat06

/-- Countable gluing of a fixed survival probability over every
measurable selection event. It applies to a residual waiting time
indexed by the observed Poisson count once each countwise
conditional survival identity has been proved. -/
theorem selected_residual_survival_of_countwise_factorisation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N)
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Measurable (F n))
    (u : ℝ) (c : ℝ≥0∞)
    (hFactor : ∀ n : ℕ,
      P {ω | N ω = n ∧ u < F n ω} =
        P {ω | N ω = n} * c) :
    P {ω | u < F (N ω) ω} = c := by
  let A (n : ℕ) : Set Ω := {ω | N ω = n ∧ u < F n ω}
  have hNm (n : ℕ) : MeasurableSet {ω | N ω = n} :=
    hN (measurableSet_singleton n)
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    (hNm n).inter ((hF n) measurableSet_Ioi)
  have hAd : Pairwise (fun i j : ℕ => Disjoint (A i) (A j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro ω hi hj
    exact hij (hi.1.symm.trans hj.1)
  have hAeq :
      {ω | u < F (N ω) ω} = ⋃ n : ℕ, A n := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, A]
    constructor
    · intro hω
      exact ⟨N ω, rfl, hω⟩
    · rintro ⟨n, hn, hω⟩
      rw [hn]
      exact hω
  have hNd : Pairwise (fun i j : ℕ =>
      Disjoint {ω | N ω = i} {ω | N ω = j}) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro ω hi hj
    exact hij (hi.symm.trans hj)
  have hNuniv : (⋃ n : ℕ, {ω | N ω = n}) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨N ω, rfl⟩
  have hSum : (∑' n : ℕ, P {ω | N ω = n}) = 1 := by
    rw [← measure_iUnion hNd hNm, hNuniv, measure_univ]
  calc
    P {ω | u < F (N ω) ω} =
        ∑' n : ℕ, P (A n) := by
      rw [hAeq, measure_iUnion hAd hAm]
    _ = ∑' n : ℕ, P {ω | N ω = n} * c := by
      congr 1
      funext n
      exact hFactor n
    _ = c := by rw [ENNReal.tsum_mul_right, hSum, one_mul]

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N)
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Measurable (F n))
    (u : ℝ) (c : ℝ≥0∞)
    (hFactor : ∀ n : ℕ,
      P {ω | N ω = n ∧ u < F n ω} =
        P {ω | N ω = n} * c) :
    P {ω | u < F (N ω) ω} = c := by
  exact selected_residual_survival_of_countwise_factorisation
    N hN F hF u c hFactor
