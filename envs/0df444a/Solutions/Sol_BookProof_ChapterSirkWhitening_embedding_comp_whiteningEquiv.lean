-- Prove2me | solution 1 for BookProof.ChapterSirkWhitening.embedding_comp_whiteningEquiv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T01:38:03.328491+00:00
-- url     : https://prove2.me/submissions/fc58cd08-539a-4774-aab9-0a0cf47c3ab0

-- Generated from ChapterSirkWhitening.lean — solution of BookProof.ChapterSirkWhitening.embedding_comp_whiteningEquiv
import Mathlib
import Definitions.Def_ChapterSirkWhitening
open BookProof.ChapterSirkWhitening








noncomputable section


open BookProof.ChapterH4

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

set_option maxHeartbeats 1000000 in
theorem solution (V₁ : F →L[ℂ] E) (V₂ : G →L[ℂ] E)
    (hV₂ : V₂.adjoint.comp V₂ = ContinuousLinearMap.id ℂ G)
    (h12 : ∀ y : F, ∃ z : G, V₁ y = V₂ z) (y : F) :
    V₂ (whiteningEquiv V₁ V₂ y) = V₁ y := by

  obtain ⟨z, hz⟩ := h12 y
  have h : V₂.adjoint (V₂ z) = z := congrArg (fun f : G →L[ℂ] G => f z) hV₂
  simp only [whiteningEquiv, ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [hz, h]
