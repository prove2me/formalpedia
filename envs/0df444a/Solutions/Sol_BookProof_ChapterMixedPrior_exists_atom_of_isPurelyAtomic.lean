-- Prove2me | solution 1 for BookProof.ChapterMixedPrior.exists_atom_of_isPurelyAtomic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:03:49.889406+00:00
-- url     : https://prove2.me/submissions/764d5ef0-9c38-4ddf-aba1-b3304b9a2a49

-- Generated from ChapterMixedPrior.lean — solution of BookProof.ChapterMixedPrior.exists_atom_of_isPurelyAtomic
import Mathlib
import Definitions.Def_ChapterMixedPrior
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterMixedPrior



open MeasureTheory ProbabilityTheory


open BookProof.ChapterAtomicDecomposition

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

set_option maxHeartbeats 1000000 in
theorem solution (mu : Measure X) [IsProbabilityMeasure mu]
    (h : IsPurelyAtomic mu) : (atoms mu).Nonempty := by

  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  rw [IsPurelyAtomic, hempty, Set.compl_empty] at h
  have : (1 : ENNReal) = 0 := by rw [← measure_univ (μ := mu)]; exact h
  exact one_ne_zero this
