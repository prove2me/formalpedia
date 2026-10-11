-- Prove2me | solution 1 for BookProof.ChapterMixedPrior.isProbabilityMeasure_normalizedContinuousPart
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:05:26.231094+00:00
-- url     : https://prove2.me/submissions/14c6a7bc-7fa4-4905-a8e7-db9902c4673c

-- Generated from ChapterMixedPrior.lean — solution of BookProof.ChapterMixedPrior.isProbabilityMeasure_normalizedContinuousPart
import Mathlib
import Definitions.Def_ChapterMixedPrior
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterMixedPrior



open MeasureTheory ProbabilityTheory


open BookProof.ChapterAtomicDecomposition

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

set_option maxHeartbeats 1000000 in
theorem solution (mu : Measure X)
    [IsFiniteMeasure mu] (h : ¬ IsPurelyAtomic mu) :
    IsProbabilityMeasure (normalizedContinuousPart mu) := cond_isProbabilityMeasure h
