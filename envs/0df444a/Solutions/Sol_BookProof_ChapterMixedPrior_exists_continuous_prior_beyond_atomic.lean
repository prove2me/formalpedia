-- Prove2me | solution 1 for BookProof.ChapterMixedPrior.exists_continuous_prior_beyond_atomic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:05:41.112195+00:00
-- url     : https://prove2.me/submissions/d645677e-418f-4400-b87e-b8b1cfc0078c

-- Generated from ChapterMixedPrior.lean — solution of BookProof.ChapterMixedPrior.exists_continuous_prior_beyond_atomic
import Mathlib
import Definitions.Def_ChapterMixedPrior
import Theorems.Thm_BookProof_ChapterMixedPrior_atomless_prior_not_purelyAtomic
import Theorems.Thm_BookProof_ChapterMixedPrior_noAtoms_normalizedContinuousPart
import Theorems.Thm_BookProof_ChapterMixedPrior_isProbabilityMeasure_normalizedContinuousPart
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterMixedPrior



open MeasureTheory ProbabilityTheory


open BookProof.ChapterAtomicDecomposition

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

set_option maxHeartbeats 1000000 in
theorem solution (mu : Measure X) [IsProbabilityMeasure mu]
    (h : ¬ IsPurelyAtomic mu) :
    ∃ nu : Measure X, IsProbabilityMeasure nu ∧ NullSingletonClass nu ∧ ¬ IsPurelyAtomic nu := by

  haveI hpm : IsProbabilityMeasure (normalizedContinuousPart mu) :=
    isProbabilityMeasure_normalizedContinuousPart mu h
  haveI hns : NullSingletonClass (normalizedContinuousPart mu) :=
    noAtoms_normalizedContinuousPart mu
  exact ⟨normalizedContinuousPart mu, hpm, hns,
    atomless_prior_not_purelyAtomic _⟩
