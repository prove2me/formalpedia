-- Prove2me | solution 1 for BookProof.ChapterAtomicDecomposition.noAtoms_continuousPart
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:04:27.833423+00:00
-- url     : https://prove2.me/submissions/c941e9b9-7e80-4d14-b990-37431da66b72

-- Generated from ChapterAtomicDecomposition.lean — theorem BookProof.ChapterAtomicDecomposition.noAtoms_continuousPart
import Mathlib
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition


open MeasureTheory


variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]


theorem solution (mu : Measure X) [SFinite mu] : NullSingletonClass (continuousPart mu) := by
  constructor
  intro x
  by_cases hx : x ∈ atoms mu
  · rw [continuousPart, Measure.restrict_apply (measurableSet_singleton x)]
    have he : ({x} : Set X) ∩ (atoms mu)ᶜ = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_compl_iff,
        Set.mem_empty_iff_false, iff_false, not_and, not_not]
      rintro rfl
      exact hx
    simp [he]
  · apply le_antisymm _ zero_le
    apply le_trans (Measure.restrict_apply_le _ _)
    exact not_lt.mp hx

#print axioms solution
