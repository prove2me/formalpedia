-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.transitionMass_sum
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:18:36.086061+00:00
-- url     : https://prove2.me/submissions/83ac129e-8c46-456f-a4d6-cfbe028b6d28

import Definitions.Def_CountingLLL_ReciprocalTransition
import Theorems.Thm_CountingLLL_ReciprocalTest_encoded_read_marginals
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

deriving instance Encodable for Context
deriving instance Encodable for Phase
deriving instance Encodable for State

/-- Every operational state has a normalized one-step transition mass. -/
theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) (s : State) :
    (∑' s' : State, transitionMass B s s') = 1 := by
  classical
  cases hq : readIndex s with
  | none =>
    simp [transitionMass, hq]
  | some a =>
    let ν := readLaw B a
    letI : IsProbabilityMeasure ν := (encoded_read_marginals B hB).1 a
    let F : State → Set ℕ := fun s' => {v | step (uniformEntropy v) s = s'}
    have hm (s' : State) : MeasurableSet (F s') := (Set.to_countable _).measurableSet
    have hd : Pairwise (fun s' t' => Disjoint (F s') (F t')) := by
      intro s' t' hne
      apply Set.disjoint_left.mpr
      intro v hv hw
      exact hne (hv.symm.trans hw)
    have hu : (⋃ s', F s') = Set.univ := by
      ext v
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact ⟨step (uniformEntropy v) s, rfl⟩
    have hsum : (∑' s', ν (F s')) = 1 := by
      rw [← measure_iUnion hd hm, hu, measure_univ]
    simpa [transitionMass, hq, F, ν] using hsum
