-- Prove2me | solution 1 for BookProof.ChapterMixedPrior.eq_zero_of_noAtoms_of_isPurelyAtomic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:03:47.769959+00:00
-- url     : https://prove2.me/submissions/daa7c161-f08c-48b6-8c4d-caacace1fac6

-- Generated from ChapterMixedPrior.lean — solution of BookProof.ChapterMixedPrior.eq_zero_of_noAtoms_of_isPurelyAtomic
import Mathlib
import Definitions.Def_ChapterMixedPrior
import Theorems.Thm_BookProof_ChapterMixedPrior_atoms_eq_empty_of_noAtoms
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterMixedPrior



open MeasureTheory ProbabilityTheory


open BookProof.ChapterAtomicDecomposition

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

set_option maxHeartbeats 1000000 in
theorem solution (mu : Measure X) [NullSingletonClass mu]
    (h : IsPurelyAtomic mu) : mu = 0 := by

  have huniv : mu Set.univ = 0 := by
    rw [IsPurelyAtomic, atoms_eq_empty_of_noAtoms mu, Set.compl_empty] at h
    exact h
  exact Measure.measure_univ_eq_zero.mp huniv
