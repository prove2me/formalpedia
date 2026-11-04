-- Prove2me | solution 1 for BookProof.ChapterStandardBorelClassification.spectral_multiplication_model_classified
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T20:49:37.274208+00:00
-- url     : https://prove2.me/submissions/75c2273c-d0aa-4e2a-b433-104a809b2133

-- Generated from ChapterStandardBorelClassification.lean — solution of BookProof.ChapterStandardBorelClassification.spectral_multiplication_model_classified
import Mathlib
import Definitions.Def_ChapterStandardBorelClassification
import Theorems.Thm_BookProof_ChapterSpectralDirectSum_spectral_multiplication_model_general_inc
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Definitions.Def_ChapterAtomicDiagonalModel
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterAbelianClassificationList
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
open BookProof.ChapterStandardBorelClassification



noncomputable section

open MeasureTheory


open BookProof.ChapterMeasureAtomicDiffuse BookProof.ChapterAtomicDiagonalModel
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterAbelianClassificationList
open BookProof.ChapterAbelianGelfandModel
open BookProof.ChapterSpectralMultiplication
open BookProof.ChapterSpectralDirectSum

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (e : X ≃ᵐ Y)
  (mu : Measure X)
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  (mu : Measure X) [IsProbabilityMeasure mu]
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
  [TopologicalSpace.MetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution (T : H →L[ℂ] H) (hT : IsStarNormal T) :
    ∃ (S : Set H) (mu : S → Measure (spectrum ℂ T))
      (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] H),
      (∀ x : S, IsProbabilityMeasure (mu x)) ∧
      IsHilbertSum ℂ (fun x : S => Lp ℂ 2 (mu x)) V ∧
      (∀ (x : S) (u : Lp ℂ 2 (mu x)),
        V x (mulRep (mu x) (coordFn T) u) = T (V x u)) ∧
      (∀ x : S, ∃ _ : IsProbabilityMeasure (mu x), RealizesStandardType (mu x)) := by

  obtain ⟨S, mu, V, hprob, hsum, hint⟩ := spectral_multiplication_model_general_inc T hT
  refine ⟨S, mu, V, hprob, hsum, hint, fun x => ?_⟩
  haveI := hprob x
  exact ⟨hprob x, standardBorel_classification_list (mu x)⟩
