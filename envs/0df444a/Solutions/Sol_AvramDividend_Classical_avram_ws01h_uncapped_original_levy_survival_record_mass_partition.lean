-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_uncapped_original_levy_survival_record_mass_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T12:46:10.463453+00:00
-- url     : https://prove2.me/submissions/6fede87a-acc2-4df1-a66f-773738b047ca

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_finite_clock_survival_killed_record_or_no_record_partition
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_uncapped_of_le_horizon
import Theorems.Thm_AvramDividend_Classical_chat04_closed_history_lower_survival_joint_measurable_ws01a
import Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- No arbitrary finite horizon remains: at the genuine observation age, actual
lower nonruin partitions into a lower-killed upper record followed by fresh
survival and a weak no-record remainder. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x b : ℝ) (hb : 0 ≤ b)
    (μ : Measure (Ω × ℝ)) :
    (let age : Ω → ℝ≥0 := fun ω =>
       (twoSidedExitUpTime X b ω).toNNReal
     let E : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}
     let A : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       twoSidedExitUpTime X b z.1 < (Real.toNNReal z.2 : ℝ≥0∞) ∧
       twoSidedExitUpTime X b z.1 < twoSidedExitDownTime X (-x) z.1 ∧
       ∀ u : ℝ≥0, u ≤ Real.toNNReal z.2 - age z.1 →
          0 ≤ (x + b) + (X.X (age z.1 + u) z.1 - X.X (age z.1) z.1)}
     let B : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       (Real.toNNReal z.2 : ℝ≥0∞) ≤ twoSidedExitUpTime X b z.1 ∧
       ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}
     μ E = μ A + μ B) := by
  intro age E A B
  have hC : MeasurableSet E := by
    simpa only [E] using
      (chat04_closed_history_lower_survival_joint_measurable_ws01a X x)
  have hUpper : MeasurableSet
      {z : Ω × ℝ |
        (Real.toNNReal z.2 : ℝ≥0∞) ≤
          twoSidedExitUpTime X b z.1} := by
    have hT : Measurable (fun z : Ω × ℝ =>
        twoSidedExitUpTime X b z.1) :=
      (upperPassage_measurable_from_stopping X b).comp measurable_fst
    exact measurableSet_le (by fun_prop) hT
  have hB : MeasurableSet B := by
    have heq : B = E ∩
        {z : Ω × ℝ | (Real.toNNReal z.2 : ℝ≥0∞) ≤
          twoSidedExitUpTime X b z.1} := by
      ext z
      simp only [B, E, Set.mem_setOf_eq, Set.mem_inter_iff]
      tauto
    rw [heq]
    exact hC.inter hUpper
  have hEqClock (z : Ω × ℝ)
      (hUp : twoSidedExitUpTime X b z.1 <
        (Real.toNNReal z.2 : ℝ≥0∞)) :
      (min (twoSidedExitUpTime X b z.1)
        (Real.toNNReal z.2 : ℝ≥0∞)).toNNReal = age z.1 := by
    have hcap : twoSidedExitUpTime X b z.1 ≤
        (Real.toNNReal z.2 : ℝ≥0∞) := hUp.le
    have hread := firstRecord_capped_clock_eq_uncapped_of_le_horizon
      X b (Real.toNNReal z.2) z.1 hcap
    have h := congrArg ENNReal.toNNReal hread
    simpa only [age, ENNReal.toNNReal_coe] using h
  have hPart : E = A ∪ B := by
    ext z
    constructor
    · intro he
      change 0 ≤ z.2 ∧
        (∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 →
          -x ≤ X.X s z.1) at he
      rcases he with ⟨ht0, hs⟩
      have hs' : ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 →
          0 ≤ x + X.X s z.1 := by
        intro s hst
        have h := hs s hst
        linarith
      have hp := (avram_ws01h_finite_clock_survival_killed_record_or_no_record_partition
        X x b hb (Real.toNNReal z.2) z.1
          (Real.toNNReal z.2) le_rfl).mp hs'
      rcases hp with h | h
      · obtain ⟨hUp, hKill, hFuture⟩ := h
        have hτ := hEqClock z hUp
        left
        refine ⟨ht0, hUp, hKill, ?_⟩
        simpa only [hτ] using hFuture
      · exact Or.inr ⟨ht0, h.1, hs⟩
    · intro he
      rcases he with ha | hb'
      · rcases ha with ⟨ht0, hUp, hKill, hFuture⟩
        have hτ := hEqClock z hUp
        have hfresh : ∀ u : ℝ≥0,
            u ≤ Real.toNNReal z.2 -
              (min (twoSidedExitUpTime X b z.1)
                (Real.toNNReal z.2 : ℝ≥0∞)).toNNReal →
            0 ≤ (x + b) +
              (X.X ((min (twoSidedExitUpTime X b z.1)
                (Real.toNNReal z.2 : ℝ≥0∞)).toNNReal + u) z.1 -
              X.X (min (twoSidedExitUpTime X b z.1)
                (Real.toNNReal z.2 : ℝ≥0∞)).toNNReal z.1) := by
          simpa only [hτ] using hFuture
        have hs' :=
          (avram_ws01h_finite_clock_survival_killed_record_or_no_record_partition
            X x b hb (Real.toNNReal z.2) z.1
              (Real.toNNReal z.2) le_rfl).mpr
                (Or.inl ⟨hUp, hKill, hfresh⟩)
        refine ⟨ht0, ?_⟩
        intro s hst
        have h := hs' s hst
        linarith
      · exact ⟨hb'.1, hb'.2.2⟩
  have hDisj : Disjoint A B := Set.disjoint_left.mpr (by
    intro z ha hb'
    exact (not_lt_of_ge hb'.2.1) ha.2.1)
  calc
    μ E = μ (A ∪ B) := congrArg μ hPart
    _ = μ A + μ B := measure_union hDisj hB
