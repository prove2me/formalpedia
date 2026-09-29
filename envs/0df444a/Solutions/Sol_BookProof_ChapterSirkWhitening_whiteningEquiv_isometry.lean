-- Prove2me | solution 1 for BookProof.ChapterSirkWhitening.whiteningEquiv_isometry
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T03:59:08.295145+00:00
-- url     : https://prove2.me/submissions/abccc71c-531f-4265-9a5a-db39bbca0def

-- Generated from ChapterSirkWhitening.lean — solution of BookProof.ChapterSirkWhitening.whiteningEquiv_isometry
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
    (hV₁ : ∀ y : F, ‖V₁ y‖ = ‖y‖) (hV₂ : ∀ z : G, ‖V₂ z‖ = ‖z‖)
    (hV₂adj : V₂.adjoint.comp V₂ = ContinuousLinearMap.id ℂ G)
    (h12 : ∀ y : F, ∃ z : G, V₁ y = V₂ z) (y : F) :
    ‖whiteningEquiv V₁ V₂ y‖ = ‖y‖ := by

  have := embedding_comp_whiteningEquiv V₁ V₂ hV₂adj h12 y
  rw [← hV₂ (whiteningEquiv V₁ V₂ y), this, hV₁]
