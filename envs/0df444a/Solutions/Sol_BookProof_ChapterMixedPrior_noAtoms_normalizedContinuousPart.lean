-- Prove2me | solution 1 for BookProof.ChapterMixedPrior.noAtoms_normalizedContinuousPart
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:05:25.159399+00:00
-- url     : https://prove2.me/submissions/46b5500b-0266-49dc-8a2e-a5c85837e387

-- Generated from ChapterMixedPrior.lean — solution of BookProof.ChapterMixedPrior.noAtoms_normalizedContinuousPart
import Mathlib
import Definitions.Def_ChapterMixedPrior
import Theorems.Thm_BookProof_ChapterAtomicDecomposition_noAtoms_continuousPart
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterMixedPrior



open MeasureTheory ProbabilityTheory


open BookProof.ChapterAtomicDecomposition

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

set_option maxHeartbeats 1000000 in
theorem solution (mu : Measure X) [SFinite mu] :
    NullSingletonClass (normalizedContinuousPart mu) := by

  have hcont : NullSingletonClass (continuousPart mu) := noAtoms_continuousPart mu
  refine NullSingletonClass.mk fun x => ?_
  have : normalizedContinuousPart mu {x}
      = (mu (atoms mu)ᶜ)⁻¹ * (continuousPart mu) {x} := by
    rw [normalizedContinuousPart, cond_apply' (measurableSet_singleton x), continuousPart,
      Measure.restrict_apply (measurableSet_singleton x), Set.inter_comm]
  rw [this, hcont.measure_singleton x, mul_zero]
