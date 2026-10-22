-- Prove2me | solution 1 for BookProof.ChapterSchurRepresentation.schur_imprimitivity
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:28:18.510758+00:00
-- url     : https://prove2.me/submissions/63fe14d8-be05-43f9-85ce-fad73d33d890

-- Generated from ChapterSchurRepresentation.lean — solution of BookProof.ChapterSchurRepresentation.schur_imprimitivity
import Mathlib
import Definitions.Def_ChapterSchurRepresentation
import Theorems.Thm_BookProof_ChapterSchurRepresentation_imprimitivitySystem_isNormal
import Theorems.Thm_BookProof_ChapterSchurIrreducible_commutant_scalar_of_irreducible
import Definitions.Def_ChapterSchurIrreducible
import Definitions.Def_ChapterA
open BookProof.ChapterSchurRepresentation



open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System BookProof.ChapterSchurIrreducible
open BookProof.ChapterA
open BookProof.ChapterA.System

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {G : Type*} [Group G] {X : Type*}
    (U : G →* (V ≃ₗᵢ[ℂ] V)) (pvm : Set X → (V →L[ℂ] V))
    (hpvm : ∀ A : Set X, IsSelfAdjoint (pvm A))
    (hirr : (imprimitivitySystem U pvm).IsIrreducible) {S : V →L[ℂ] V}
    (hU : ∀ g : G, S * uCLM (U g) = uCLM (U g) * S)
    (hP : ∀ A : Set X, S * pvm A = pvm A * S) :
    ∃ c : ℂ, S = c • (1 : V →L[ℂ] V) :=
  commutant_scalar_of_irreducible (imprimitivitySystem U pvm)
      (imprimitivitySystem_isNormal U pvm hpvm) hirr
      (by
        rintro m (⟨g, rfl⟩ | ⟨A, rfl⟩)
        · exact hU g
        · exact hP A)
