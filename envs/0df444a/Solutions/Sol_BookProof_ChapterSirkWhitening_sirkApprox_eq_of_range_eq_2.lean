-- Prove2me | solution 2 for BookProof.ChapterSirkWhitening.sirkApprox_eq_of_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T04:56:54.598852+00:00
-- url     : https://prove2.me/submissions/db0f0b5f-2b0d-4b20-a8db-e9a8be05c2e7

-- Generated from ChapterSirkWhitening.lean — solution of BookProof.ChapterSirkWhitening.sirkApprox_eq_of_range_eq
import Mathlib
import Definitions.Def_ChapterSirkWhitening
import Theorems.Thm_BookProof_ChapterSirkWhitening_rangeProj_eq_of_range_eq
import Theorems.Thm_BookProof_ChapterSirkWhitening_compress_reconstruct_eq
open BookProof.ChapterSirkWhitening








noncomputable section


open BookProof.ChapterH4

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

set_option maxHeartbeats 1000000 in
theorem solution (V₁ : F →L[ℂ] E) (V₂ : G →L[ℂ] E) (X : E →L[ℂ] E)
    (hV₁ : V₁.adjoint.comp V₁ = ContinuousLinearMap.id ℂ F)
    (hV₂ : V₂.adjoint.comp V₂ = ContinuousLinearMap.id ℂ G)
    (h12 : ∀ y : F, ∃ z : G, V₁ y = V₂ z)
    (h21 : ∀ z : G, ∃ y : F, V₂ z = V₁ y) :
    V₁.comp ((compress V₁ X).comp V₁.adjoint)
      = V₂.comp ((compress V₂ X).comp V₂.adjoint) := by

  rw [compress_reconstruct_eq, compress_reconstruct_eq,
    rangeProj_eq_of_range_eq V₁ V₂ hV₁ hV₂ h12 h21]
