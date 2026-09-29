-- Prove2me | solution 1 for BookProof.ChapterSirkWhitening.whiteningEquiv_left_inverse
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T04:00:38.909493+00:00
-- url     : https://prove2.me/submissions/68e0abf7-9937-477b-9c39-a950548c68e8

-- Generated from ChapterSirkWhitening.lean — solution of BookProof.ChapterSirkWhitening.whiteningEquiv_left_inverse
import Mathlib
import Definitions.Def_ChapterSirkWhitening
import Theorems.Thm_BookProof_ChapterSirkWhitening_embedding_comp_whiteningEquiv
open BookProof.ChapterSirkWhitening








noncomputable section


open BookProof.ChapterH4

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

set_option maxHeartbeats 1000000 in
theorem solution (V₁ : F →L[ℂ] E) (V₂ : G →L[ℂ] E)
    (hV₁ : V₁.adjoint.comp V₁ = ContinuousLinearMap.id ℂ F)
    (hV₂ : V₂.adjoint.comp V₂ = ContinuousLinearMap.id ℂ G)
    (h12 : ∀ y : F, ∃ z : G, V₁ y = V₂ z) (y : F) :
    whiteningEquiv V₂ V₁ (whiteningEquiv V₁ V₂ y) = y := by

  have h := embedding_comp_whiteningEquiv V₁ V₂ hV₂ h12 y
  have h' : V₁.adjoint (V₁ y) = y := congrArg (fun f : F →L[ℂ] F => f y) hV₁
  change V₁.adjoint (V₂ (whiteningEquiv V₁ V₂ y)) = y
  rw [h, h']
