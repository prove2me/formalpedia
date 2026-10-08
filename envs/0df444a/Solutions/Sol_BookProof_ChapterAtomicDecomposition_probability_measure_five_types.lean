-- Prove2me | solution 1 for BookProof.ChapterAtomicDecomposition.probability_measure_five_types
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:04:37.20697+00:00
-- url     : https://prove2.me/submissions/8643daa5-9460-4e65-b3ec-927f659a67d3

-- Generated from ChapterAtomicDecomposition.lean — theorem BookProof.ChapterAtomicDecomposition.probability_measure_five_types
import Mathlib
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition


open MeasureTheory


variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]


theorem solution (mu : Measure X) [IsProbabilityMeasure mu] :
    (continuousPart mu = 0 ∧ (atoms mu).Finite ∧ (atoms mu).Nonempty) ∨
    (continuousPart mu = 0 ∧ (atoms mu).Infinite) ∨
    (continuousPart mu ≠ 0 ∧ atoms mu = ∅) ∨
    (continuousPart mu ≠ 0 ∧ (atoms mu).Finite ∧ (atoms mu).Nonempty) ∨
    (continuousPart mu ≠ 0 ∧ (atoms mu).Infinite) := by
  classical
  have hn : ¬ (continuousPart mu = 0 ∧ atoms mu = ∅) := by
    rintro ⟨hc, ha⟩
    have hmu : mu = 0 := by
      simpa [continuousPart, ha] using hc
    have hmass := measure_univ (μ := mu)
    rw [hmu] at hmass
    simpa using hmass
  by_cases hc : continuousPart mu = 0
  · have ha : (atoms mu).Nonempty := Set.nonempty_iff_ne_empty.mpr (fun h => hn ⟨hc, h⟩)
    by_cases hf : (atoms mu).Finite
    · exact Or.inl ⟨hc, hf, ha⟩
    · exact Or.inr (Or.inl ⟨hc, hf⟩)
  · by_cases he : atoms mu = ∅
    · exact Or.inr (Or.inr (Or.inl ⟨hc, he⟩))
    · have ha := Set.nonempty_iff_ne_empty.mpr he
      by_cases hf : (atoms mu).Finite
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, hf, ha⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hc, hf⟩)))

#print axioms solution

