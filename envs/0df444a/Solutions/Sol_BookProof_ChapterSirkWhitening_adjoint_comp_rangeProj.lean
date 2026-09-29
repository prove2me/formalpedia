-- Prove2me | solution 1 for BookProof.ChapterSirkWhitening.adjoint_comp_rangeProj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:21:28.305382+00:00
-- url     : https://prove2.me/submissions/804c82ca-ecfb-4ee1-a140-47cafc159512

-- Generated from ChapterSirkWhitening.lean — solution of BookProof.ChapterSirkWhitening.adjoint_comp_rangeProj
import Mathlib
import Definitions.Def_ChapterSirkWhitening
import Theorems.Thm_BookProof_ChapterSirkWhitening_rangeProj_adjoint
import Theorems.Thm_BookProof_ChapterSirkWhitening_rangeProj_comp_embedding
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
    (h12 : ∀ y : F, ∃ z : G, V₁ y = V₂ z) :
    V₁.adjoint.comp (rangeProj V₂) = V₁.adjoint := by

  have hfix : (rangeProj V₂).comp V₁ = V₁ := by
    ext y
    obtain ⟨z, hz⟩ := h12 y
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [hz]
    exact rangeProj_comp_embedding V₂ hV₂ z
  calc V₁.adjoint.comp (rangeProj V₂)
      = ContinuousLinearMap.adjoint ((rangeProj V₂).comp V₁) := by
        rw [ContinuousLinearMap.adjoint_comp, rangeProj_adjoint V₂]
    _ = V₁.adjoint := by rw [hfix]
