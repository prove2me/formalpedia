-- Prove2me | solution 1 for BookProof.ChapterAbelianAtomicCondensation.atomic_measure_index_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:35:56.904566+00:00
-- url     : https://prove2.me/submissions/d12ab179-686a-47a5-a93c-471373c428bf

-- Generated from ChapterAbelianAtomicCondensation.lean — solution of BookProof.ChapterAbelianAtomicCondensation.atomic_measure_index_dichotomy
import Mathlib
import Definitions.Def_ChapterAbelianAtomicCondensation
import Theorems.Thm_BookProof_ChapterAtomicDecomposition_atoms_countable
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition
open MeasureTheory
open BookProof.ChapterAbelianAtomicCondensation



open scoped ENNReal

noncomputable section


open BookProof.ChapterAbelianDiagonalCountable

set_option maxHeartbeats 1000000 in
theorem solution {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (mu : Measure X) [IsProbabilityMeasure mu] :
    (∃ n : ℕ, Nonempty (atoms mu ≃ Fin n)) ∨ Nonempty (atoms mu ≃ ℕ) := by

  have hcount : (atoms mu).Countable := atoms_countable mu
  haveI : Countable (atoms mu) := hcount.to_subtype
  rcases finite_or_infinite (atoms mu) with hfin | hinf
  · exact Or.inl (Finite.exists_equiv_fin (atoms mu))
  · haveI : Encodable (atoms mu) := Encodable.ofCountable _
    exact Or.inr ⟨(Denumerable.ofEncodableOfInfinite (atoms mu)).eqv⟩
