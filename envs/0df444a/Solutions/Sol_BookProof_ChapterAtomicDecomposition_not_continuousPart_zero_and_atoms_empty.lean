-- Prove2me | solution 1 for BookProof.ChapterAtomicDecomposition.not_continuousPart_zero_and_atoms_empty
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:04:31.850428+00:00
-- url     : https://prove2.me/submissions/75d9e7ee-0a4a-4ebd-a251-65917d469302

-- Generated from ChapterAtomicDecomposition.lean — theorem BookProof.ChapterAtomicDecomposition.not_continuousPart_zero_and_atoms_empty
import Mathlib
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition


open MeasureTheory


variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]


theorem solution (mu : Measure X) [IsProbabilityMeasure mu] :
    ¬ (continuousPart mu = 0 ∧ atoms mu = ∅) := by
  rintro ⟨hc, ha⟩
  have hmu : mu = 0 := by
    simpa [continuousPart, ha] using hc
  have hmass := measure_univ (μ := mu)
  rw [hmu] at hmass
  simpa using hmass

#print axioms solution

