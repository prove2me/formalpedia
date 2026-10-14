-- Prove2me | solution 1 for BookProof.ChapterAbelianClassificationList.vonNeumann_abelian_classification_list
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T20:18:54.394664+00:00
-- url     : https://prove2.me/submissions/69ec1ea0-be33-44c4-811a-21adaad5891a

-- Generated from ChapterAbelianClassificationList.lean — solution of BookProof.ChapterAbelianClassificationList.vonNeumann_abelian_classification_list
import Mathlib
import Definitions.Def_ChapterAbelianClassificationList
import Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_countable_atomSet
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Definitions.Def_ChapterAtomicDiagonalModel
import Definitions.Def_ChapterDiffuseUnitaryModel
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterLpRestrictSplit
import Definitions.Def_ChapterLpScaleMeasure
open BookProof.ChapterAbelianClassificationList



noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterMeasureAtomicDiffuse BookProof.ChapterAtomicDiagonalModel
open BookProof.ChapterDiffuseUnitaryModel BookProof.ChapterLinftyMultiplication
open BookProof.ChapterLpRestrictSplit BookProof.ChapterLpScaleMeasure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
variable (nu : Measure ℝ) [IsFiniteMeasure nu] [NullSingletonClass nu]
variable (mu : Measure ℝ) [IsProbabilityMeasure mu]

set_option maxHeartbeats 1000000 in
theorem solution :
    (atomSet mu).Countable ∧
      ((mu (atomSet mu)ᶜ = 0 ∧ (atomSet mu).Finite) ∨
        (mu (atomSet mu)ᶜ = 0 ∧ (atomSet mu).Infinite ∧
          Nonempty (atomSet mu ≃ ℕ)) ∨
        (mu (atomSet mu) = 0 ∧ atomSet mu = ∅) ∨
        (mu (atomSet mu) ≠ 0 ∧ mu (atomSet mu)ᶜ ≠ 0 ∧ (atomSet mu).Finite) ∨
        (mu (atomSet mu) ≠ 0 ∧ mu (atomSet mu)ᶜ ≠ 0 ∧ (atomSet mu).Infinite ∧
          Nonempty (atomSet mu ≃ ℕ))) := by

  have hcount := countable_atomSet mu
  refine ⟨hcount, ?_⟩
  have hequiv : (atomSet mu).Infinite → Nonempty (atomSet mu ≃ ℕ) := by
    intro hinf
    haveI : Countable (atomSet mu) := hcount.to_subtype
    haveI : Infinite (atomSet mu) := hinf.to_subtype
    obtain ⟨d⟩ := nonempty_denumerable (atomSet mu)
    exact ⟨d.eqv⟩
  by_cases hdiff : mu (atomSet mu)ᶜ = 0
  · rcases Set.finite_or_infinite (atomSet mu) with hfin | hinf
    · exact Or.inl ⟨hdiff, hfin⟩
    · exact Or.inr (Or.inl ⟨hdiff, hinf, hequiv hinf⟩)
  · by_cases hat : mu (atomSet mu) = 0
    · refine Or.inr (Or.inr (Or.inl ⟨hat, ?_⟩))
      -- an atom would carry positive mass inside the atom set
      by_contra hne
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
      exact hx (measure_mono_null (Set.singleton_subset_iff.2 hx) hat)
    · rcases Set.finite_or_infinite (atomSet mu) with hfin | hinf
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hat, hdiff, hfin⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hat, hdiff, hinf, hequiv hinf⟩)))
