-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_genuine_finite_clock_killed_record_mass_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:32:50.448816+00:00
-- url     : https://prove2.me/submissions/8b63c283-1417-45cf-a73d-8b71705deeb6

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_finite_clock_survival_killed_record_or_no_record_partition
import Theorems.Thm_AvramDividend_Classical_chat04_closed_history_lower_survival_joint_measurable_ws01a
import Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Exact finite-clock original Lévy nonruin mass partitions under any joint
observation law, including the genuine Esscher-terminal Qp measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (hb : 0 ≤ b) (N : ℝ≥0)
    (μ : Measure (Ω × ℝ)) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let E : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       Real.toNNReal z.2 ≤ N ∧
       ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}
     let A : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       Real.toNNReal z.2 ≤ N ∧
       twoSidedExitUpTime X b z.1 < (Real.toNNReal z.2 : ℝ≥0∞) ∧
       twoSidedExitUpTime X b z.1 < twoSidedExitDownTime X (-x) z.1 ∧
       ∀ u : ℝ≥0, u ≤ Real.toNNReal z.2 - τ z.1 →
         0 ≤ (x + b) + (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1)}
     let B : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       Real.toNNReal z.2 ≤ N ∧
       (Real.toNNReal z.2 : ℝ≥0∞) ≤ twoSidedExitUpTime X b z.1 ∧
       ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}
     μ E = μ A + μ B) := by
  intro τ E A B
  have hCap : MeasurableSet
      {z : Ω × ℝ | Real.toNNReal z.2 ≤ N} := by
    exact measurableSet_le (by fun_prop) measurable_const
  have hC : MeasurableSet
      {z : Ω × ℝ | 0 ≤ z.2 ∧
        ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1} :=
    chat04_closed_history_lower_survival_joint_measurable_ws01a X x
  have hE : MeasurableSet E := by
    have hEq : E =
        {z : Ω × ℝ | 0 ≤ z.2 ∧
          ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 →
            -x ≤ X.X s z.1} ∩
        {z : Ω × ℝ | Real.toNNReal z.2 ≤ N} := by
      ext z
      simp only [E, Set.mem_setOf_eq, Set.mem_inter_iff]
      tauto
    rw [hEq]
    exact hC.inter hCap
  have hUpper : MeasurableSet
      {z : Ω × ℝ |
        (Real.toNNReal z.2 : ℝ≥0∞) ≤
          twoSidedExitUpTime X b z.1} := by
    have hT : Measurable (fun z : Ω × ℝ =>
        twoSidedExitUpTime X b z.1) :=
      (upperPassage_measurable_from_stopping X b).comp measurable_fst
    exact measurableSet_le (by fun_prop) hT
  have hB : MeasurableSet B := by
    have hEq : B = E ∩ {z : Ω × ℝ |
        (Real.toNNReal z.2 : ℝ≥0∞) ≤
          twoSidedExitUpTime X b z.1} := by
      ext z
      simp only [E, B, Set.mem_setOf_eq, Set.mem_inter_iff]
      tauto
    rw [hEq]
    exact hE.inter hUpper
  have hPart : E = A ∪ B := by
    ext z
    constructor
    · intro he
      change 0 ≤ z.2 ∧ Real.toNNReal z.2 ≤ N ∧
        (∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 →
          -x ≤ X.X s z.1) at he
      rcases he with ⟨ht0, htN, hs⟩
      have hs' : ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 →
          0 ≤ x + X.X s z.1 := by
        intro s hst
        have h := hs s hst
        linarith
      have hp := (avram_ws01h_finite_clock_survival_killed_record_or_no_record_partition
        X x b hb N z.1 (Real.toNNReal z.2) htN).mp hs'
      rcases hp with h | h
      · exact Or.inl ⟨ht0, htN, h.1, h.2.1, h.2.2⟩
      · exact Or.inr ⟨ht0, htN, h.1, hs⟩
    · intro h
      rcases h with ha | hb'
      · rcases ha with ⟨ht0, htN, hUp, hKill, hFuture⟩
        have hs' :=
          (avram_ws01h_finite_clock_survival_killed_record_or_no_record_partition
            X x b hb N z.1 (Real.toNNReal z.2) htN).mpr
              (Or.inl ⟨hUp, hKill, hFuture⟩)
        refine ⟨ht0, htN, ?_⟩
        intro s hst
        have h := hs' s hst
        linarith
      · exact ⟨hb'.1, hb'.2.1, hb'.2.2.2⟩
  have hDisj : Disjoint A B := Set.disjoint_left.mpr (by
    intro z ha hb'
    rcases ha with ⟨_, _, hBefore, _, _⟩
    rcases hb' with ⟨_, _, hAfter, _⟩
    exact (not_lt_of_ge hAfter) hBefore)
  have hAeq : A = E \ B := by
    ext z
    constructor
    · intro ha
      have he : z ∈ E := by
        rw [hPart]
        exact Or.inl ha
      exact ⟨he, fun hb' => (Set.disjoint_left.mp hDisj) ha hb'⟩
    · rintro ⟨he, hnb⟩
      rw [hPart] at he
      rcases he with ha | hb'
      · exact ha
      · exact False.elim (hnb hb')
  have hA : MeasurableSet A := by
    rw [hAeq]
    exact hE.diff hB
  calc
    μ E = μ (A ∪ B) := congrArg μ hPart
    _ = μ A + μ B := measure_union hDisj hB
