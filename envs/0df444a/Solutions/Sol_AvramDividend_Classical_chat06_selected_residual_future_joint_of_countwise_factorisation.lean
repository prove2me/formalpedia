-- Prove2me | solution 1 for AvramDividend.Classical.chat06_selected_residual_future_joint_of_countwise_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:21:30.272019+00:00
-- url     : https://prove2.me/submissions/4cf74eb9-a834-43a0-b309-195ab8fc4662

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace AvramChat06

/-- Countable selection glues a common joint law for residual
survival and an arbitrary whole-future event across all count
cylinders. The input is the indexwise joint factorisation. -/
theorem selected_residual_future_joint_of_countwise_factorisation
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N)
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Measurable (F n))
    (G : ℕ → Ω → E) (hG : ∀ n, Measurable (G n))
    (B : Set E) (hB : MeasurableSet B)
    (u : ℝ) (c d : ℝ≥0∞)
    (hFactor : ∀ n : ℕ,
      P {ω | N ω = n ∧ u < F n ω ∧ G n ω ∈ B} =
        (P {ω | N ω = n} * c) * d) :
    P {ω | u < F (N ω) ω ∧ G (N ω) ω ∈ B} = c * d := by
  let A (n : ℕ) : Set Ω :=
    {ω | N ω = n ∧ u < F n ω ∧ G n ω ∈ B}
  have hNm (n : ℕ) : MeasurableSet {ω | N ω = n} :=
    hN (measurableSet_singleton n)
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    (hNm n).inter (((hF n) measurableSet_Ioi).inter ((hG n) hB))
  have hAd : Pairwise (fun i j : ℕ => Disjoint (A i) (A j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro ω hi hj
    exact hij (hi.1.symm.trans hj.1)
  have hAeq :
      {ω | u < F (N ω) ω ∧ G (N ω) ω ∈ B} =
        ⋃ n : ℕ, A n := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, A]
    constructor
    · rintro ⟨hu, hb⟩
      exact ⟨N ω, rfl, hu, hb⟩
    · rintro ⟨n, hn, hu, hb⟩
      rw [hn]
      exact ⟨hu, hb⟩
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
    P {ω | u < F (N ω) ω ∧ G (N ω) ω ∈ B} =
        ∑' n : ℕ, P (A n) := by
      rw [hAeq, measure_iUnion hAd hAm]
    _ = ∑' n : ℕ, (P {ω | N ω = n} * c) * d := by
      congr 1
      funext n
      exact hFactor n
    _ = (∑' n : ℕ, P {ω | N ω = n} * c) * d := by
      rw [ENNReal.tsum_mul_right]
    _ = ((∑' n : ℕ, P {ω | N ω = n}) * c) * d := by
      rw [ENNReal.tsum_mul_right]
    _ = c * d := by rw [hSum, one_mul]

end AvramChat06

open AvramChat06

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N)
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Measurable (F n))
    (G : ℕ → Ω → E) (hG : ∀ n, Measurable (G n))
    (B : Set E) (hB : MeasurableSet B)
    (u : ℝ) (c d : ℝ≥0∞)
    (hFactor : ∀ n : ℕ,
      P {ω | N ω = n ∧ u < F n ω ∧ G n ω ∈ B} =
        (P {ω | N ω = n} * c) * d) :
    P {ω | u < F (N ω) ω ∧ G (N ω) ω ∈ B} = c * d := by
  exact selected_residual_future_joint_of_countwise_factorisation
    N hN F hF G hG B hB u c d hFactor
