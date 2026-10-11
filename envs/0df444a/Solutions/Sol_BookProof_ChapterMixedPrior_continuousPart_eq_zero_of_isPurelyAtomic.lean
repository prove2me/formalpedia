-- Prove2me | solution 1 for BookProof.ChapterMixedPrior.continuousPart_eq_zero_of_isPurelyAtomic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:03:45.728024+00:00
-- url     : https://prove2.me/submissions/3c06cc0e-3704-4923-a487-a00b5251dbb8

-- Generated from ChapterMixedPrior.lean — solution of BookProof.ChapterMixedPrior.continuousPart_eq_zero_of_isPurelyAtomic
import Mathlib
import Definitions.Def_ChapterMixedPrior
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterMixedPrior



open MeasureTheory ProbabilityTheory


open BookProof.ChapterAtomicDecomposition

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

set_option maxHeartbeats 1000000 in
theorem solution {mu : Measure X} (h : IsPurelyAtomic mu) :
    continuousPart mu = 0 := Measure.restrict_eq_zero.2 h
