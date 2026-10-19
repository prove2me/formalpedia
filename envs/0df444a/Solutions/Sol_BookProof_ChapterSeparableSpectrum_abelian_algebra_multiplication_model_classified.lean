-- Prove2me | solution 1 for BookProof.ChapterSeparableSpectrum.abelian_algebra_multiplication_model_classified
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T09:56:55.840016+00:00
-- url     : https://prove2.me/submissions/29fc6ef2-6d87-46ae-8048-f7a84605f265

-- Generated from ChapterSeparableSpectrum.lean — solution of BookProof.ChapterSeparableSpectrum.abelian_algebra_multiplication_model_classified
import Mathlib
import Definitions.Def_ChapterSeparableSpectrum
import Theorems.Thm_BookProof_ChapterSeparableSpectrum_metrizableSpace_characterSpace
import Theorems.Thm_BookProof_ChapterAbelianDirectSum_abelian_algebra_multiplication_model_general
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterAbelianDirectSum
import Definitions.Def_ChapterStandardBorelClassification
open BookProof.ChapterSeparableSpectrum



noncomputable section

open MeasureTheory TopologicalSpace WeakDual


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterAbelianDirectSum
open BookProof.ChapterStandardBorelClassification

variable (Y : Type*) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
  [SeparableSpace C(Y, ℂ)] [MeasurableSpace Y] [BorelSpace Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : Type*) [CommCStarAlgebra A]
variable {A}

set_option maxHeartbeats 1000000 in
theorem solution [SeparableSpace A]
    (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    ∃ (S : Set H) (mu : S → Measure (characterSpace ℂ A))
      (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] H),
      (∀ x : S, IsProbabilityMeasure (mu x)) ∧
      IsHilbertSum ℂ (fun x : S => Lp ℂ 2 (mu x)) V ∧
      (∀ (x : S) (a : A) (u : Lp ℂ 2 (mu x)),
        V x (mulRep (mu x) (gelfandModel A a) u) = rho a (V x u)) ∧
      (∀ x : S, ∃ _ : IsProbabilityMeasure (mu x), RealizesStandardType (mu x)) := by

  haveI : MetrizableSpace (characterSpace ℂ A) := metrizableSpace_characterSpace A
  letI := metrizableSpaceMetric (characterSpace ℂ A)
  haveI : PolishSpace (characterSpace ℂ A) := inferInstance
  haveI : StandardBorelSpace (characterSpace ℂ A) := inferInstance
  obtain ⟨S, mu, V, hprob, hsum, hint⟩ := abelian_algebra_multiplication_model_general rho
  refine ⟨S, mu, V, hprob, hsum, hint, fun x => ?_⟩
  haveI := hprob x
  exact ⟨hprob x, standardBorel_classification_list (mu x)⟩
