-- Prove2me | solution 1 for BookProof.ChapterSelectingEvents.exists_continuous_atomic_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:30:55.385793+00:00
-- url     : https://prove2.me/submissions/c468be10-37b2-4250-95ab-4f3371600577

-- Generated from ChapterSelectingEvents.lean — solution of BookProof.ChapterSelectingEvents.exists_continuous_atomic_decomposition
import Mathlib
import Definitions.Def_ChapterSelectingEvents
open BookProof.ChapterSelectingEvents



open scoped BigOperators
open MeasureTheory ProbabilityTheory


variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Ω Data : Type*} [MeasurableSpace Ω]
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

set_option maxHeartbeats 1000000 in
theorem solution [MeasurableSingletonClass X] :
    ∃ cont atom : Measure X, μ = cont + atom ∧ NullSingletonClass cont ∧
      ∃ A : Set X, A.Countable ∧ atom Aᶜ = 0 := by

  classical
  set A : Set X := {x | 0 < μ {x}} with hA
  have hcount : A.Countable := by
    have := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ)
      (As := fun x : X => ({x} : Set X)) (fun x => measurableSet_singleton x)
      (by intro x y hxy; simpa [Function.onFun] using hxy)
    simpa [hA] using this
  have hmeas : MeasurableSet A := hcount.measurableSet
  refine ⟨μ.restrict Aᶜ, μ.restrict A, ?_, ?_, A, hcount, ?_⟩
  · rw [add_comm]
    exact (Measure.restrict_add_restrict_compl hmeas).symm
  · constructor
    intro x
    rcases eq_or_ne (μ {x}) 0 with h | h
    · exact le_antisymm (le_trans (Measure.restrict_apply_le _ _) (le_of_eq h)) zero_le
    · have hxA : x ∈ A := by
        simp only [hA, Set.mem_ofPred_eq]
        exact pos_iff_ne_zero.mpr h
      rw [Measure.restrict_apply (measurableSet_singleton x)]
      have hempty : ({x} : Set X) ∩ Aᶜ = ∅ := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_compl_iff,
          Set.mem_empty_iff_false, iff_false, not_and, not_not]
        rintro rfl; exact hxA
      simp [hempty]
  · rw [Measure.restrict_apply hmeas.compl]
    simp
