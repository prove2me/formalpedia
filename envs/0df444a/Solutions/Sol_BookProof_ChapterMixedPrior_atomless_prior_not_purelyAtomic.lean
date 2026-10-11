-- Prove2me | solution 1 for BookProof.ChapterMixedPrior.atomless_prior_not_purelyAtomic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:03:48.845053+00:00
-- url     : https://prove2.me/submissions/ce6757d4-e4f0-4852-ba3a-652e7081410d

-- Generated from ChapterMixedPrior.lean — solution of BookProof.ChapterMixedPrior.atomless_prior_not_purelyAtomic
import Mathlib
import Definitions.Def_ChapterMixedPrior
import Theorems.Thm_BookProof_ChapterMixedPrior_eq_zero_of_noAtoms_of_isPurelyAtomic
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterMixedPrior



open MeasureTheory ProbabilityTheory


open BookProof.ChapterAtomicDecomposition

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

set_option maxHeartbeats 1000000 in
theorem solution (mu : Measure X) [IsProbabilityMeasure mu]
    [NullSingletonClass mu] : ¬ IsPurelyAtomic mu := by

  intro h
  have hzero := eq_zero_of_noAtoms_of_isPurelyAtomic mu h
  have : (1 : ENNReal) = 0 := by rw [← measure_univ (μ := mu), hzero]; simp
  exact one_ne_zero this
