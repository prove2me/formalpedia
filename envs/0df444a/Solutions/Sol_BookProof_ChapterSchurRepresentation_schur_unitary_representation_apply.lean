-- Prove2me | solution 1 for BookProof.ChapterSchurRepresentation.schur_unitary_representation_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:28:16.485096+00:00
-- url     : https://prove2.me/submissions/f7f87d7e-90d4-4473-9ce7-3562ed3f7422

-- Generated from ChapterSchurRepresentation.lean — solution of BookProof.ChapterSchurRepresentation.schur_unitary_representation_apply
import Mathlib
import Definitions.Def_ChapterSchurRepresentation
import Theorems.Thm_BookProof_ChapterSchurRepresentation_schur_unitary_representation
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
theorem solution {G : Type*} [Group G] (U : G →* (V ≃ₗᵢ[ℂ] V))
    (hirr : (repSystem U).IsIrreducible) {S : V →L[ℂ] V}
    (hcomm : ∀ (g : G) (x : V), S (U g x) = U g (S x)) :
    ∃ c : ℂ, ∀ x, S x = c • x := by

  obtain ⟨c, hc⟩ := schur_unitary_representation U hirr (S := S) (by
    intro g
    ext x
    simpa [ContinuousLinearMap.mul_apply] using hcomm g x)
  exact ⟨c, fun x => by simpa using congrArg (fun T : V →L[ℂ] V => T x) hc⟩
