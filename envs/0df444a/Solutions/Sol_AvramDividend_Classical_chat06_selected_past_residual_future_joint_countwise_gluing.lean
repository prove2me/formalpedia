-- Prove2me | solution 1 for AvramDividend.Classical.chat06_selected_past_residual_future_joint_countwise_gluing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:59:02.797387+00:00
-- url     : https://prove2.me/submissions/22638d2d-6d8b-4c1a-8e81-fd6fed3b3646

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Countwise factorisation against a fixed measurable past event
glues to independence of a selected residual/future event from that past event. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N)
    (H : Set Ω) (hH : MeasurableSet H)
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Measurable (F n))
    (G : ℕ → Ω → E) (hG : ∀ n, Measurable (G n))
    (B : Set E) (hB : MeasurableSet B)
    (u : ℝ) (c d : ℝ≥0∞)
    (hFactor : ∀ n : ℕ,
      P {ω | ω ∈ H ∧ N ω = n ∧ u < F n ω ∧ G n ω ∈ B} =
        (P {ω | ω ∈ H ∧ N ω = n} * c) * d) :
    P {ω | ω ∈ H ∧ u < F (N ω) ω ∧ G (N ω) ω ∈ B} =
      (P H * c) * d := by
  let A (n : ℕ) : Set Ω :=
    {ω | ω ∈ H ∧ N ω = n ∧ u < F n ω ∧ G n ω ∈ B}
  let C (n : ℕ) : Set Ω :=
    {ω | ω ∈ H ∧ N ω = n}
  have hNm (n : ℕ) : MeasurableSet {ω | N ω = n} :=
    hN (measurableSet_singleton n)
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    hH.inter ((hNm n).inter (((hF n) measurableSet_Ioi).inter ((hG n) hB)))
  have hCm (n : ℕ) : MeasurableSet (C n) :=
    hH.inter (hNm n)
  have hAd : Pairwise (fun i j : ℕ => Disjoint (A i) (A j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro ω hi hj
    exact hij (hi.2.1.symm.trans hj.2.1)
  have hCd : Pairwise (fun i j : ℕ => Disjoint (C i) (C j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro ω hi hj
    exact hij (hi.2.symm.trans hj.2)
  have hAeq :
      {ω | ω ∈ H ∧ u < F (N ω) ω ∧ G (N ω) ω ∈ B} =
        ⋃ n : ℕ, A n := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, A]
    constructor
    · rintro ⟨hh, hu, hb⟩
      exact ⟨N ω, hh, rfl, hu, hb⟩
    · rintro ⟨n, hh, hn, hu, hb⟩
      rw [hn]
      exact ⟨hh, hu, hb⟩
  have hCu : (⋃ n : ℕ, C n) = H := by
    ext ω
    simp only [Set.mem_iUnion, C, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hh, hn⟩
      exact hh
    · intro hh
      exact ⟨N ω, hh, rfl⟩
  have hSum : (∑' n : ℕ, P (C n)) = P H := by
    rw [← measure_iUnion hCd hCm, hCu]
  calc
    P {ω | ω ∈ H ∧ u < F (N ω) ω ∧ G (N ω) ω ∈ B} =
        ∑' n : ℕ, P (A n) := by
      rw [hAeq, measure_iUnion hAd hAm]
    _ = ∑' n : ℕ, (P (C n) * c) * d := by
      congr 1
      funext n
      exact hFactor n
    _ = (∑' n : ℕ, P (C n) * c) * d := by
      rw [ENNReal.tsum_mul_right]
    _ = ((∑' n : ℕ, P (C n)) * c) * d := by
      rw [ENNReal.tsum_mul_right]
    _ = (P H * c) * d := by rw [hSum]
