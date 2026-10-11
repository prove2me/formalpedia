-- Prove2me | solution 1 for BookProof.ChapterMixedPrior.atoms_eq_empty_of_noAtoms
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:03:46.700222+00:00
-- url     : https://prove2.me/submissions/d747956d-2937-415e-b074-3e4530a813c7

-- Generated from ChapterMixedPrior.lean — solution of BookProof.ChapterMixedPrior.atoms_eq_empty_of_noAtoms
import Mathlib
import Definitions.Def_ChapterMixedPrior
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterMixedPrior



open MeasureTheory ProbabilityTheory


open BookProof.ChapterAtomicDecomposition

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

set_option maxHeartbeats 1000000 in
theorem solution (mu : Measure X) [NullSingletonClass mu] : atoms mu = ∅ := by

  ext x
  simp only [atoms, Set.mem_ofPred_eq, measure_singleton x, lt_self_iff_false,
    Set.mem_empty_iff_false]
