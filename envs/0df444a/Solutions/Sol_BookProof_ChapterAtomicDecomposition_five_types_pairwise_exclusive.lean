-- Prove2me | solution 1 for BookProof.ChapterAtomicDecomposition.five_types_pairwise_exclusive
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:04:35.460404+00:00
-- url     : https://prove2.me/submissions/2acb3d5f-2b8d-489e-9247-92f8abe7fffd

-- Generated from ChapterAtomicDecomposition.lean — theorem BookProof.ChapterAtomicDecomposition.five_types_pairwise_exclusive
import Mathlib
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition


open MeasureTheory


variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]


theorem solution (mu : Measure X) :
    ¬ ((atoms mu).Finite ∧ (atoms mu).Infinite) ∧
      ¬ ((atoms mu = ∅) ∧ (atoms mu).Nonempty) ∧
      ¬ ((atoms mu = ∅) ∧ (atoms mu).Infinite) ∧
      ¬ (continuousPart mu = 0 ∧ continuousPart mu ≠ 0) := by
  constructor
  · rintro ⟨hf, hi⟩
    exact hi hf
  constructor
  · rintro ⟨he, hn⟩
    simpa [he] using hn
  constructor
  · rintro ⟨he, hi⟩
    exact hi (he ▸ Set.finite_empty)
  · exact fun ⟨h, hn⟩ => hn h

#print axioms solution

