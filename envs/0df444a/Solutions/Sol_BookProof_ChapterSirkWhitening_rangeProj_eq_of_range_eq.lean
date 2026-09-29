-- Prove2me | solution 1 for BookProof.ChapterSirkWhitening.rangeProj_eq_of_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T04:12:03.271608+00:00
-- url     : https://prove2.me/submissions/5c0c6a1f-a629-42e0-b495-3cfd7ff6b85b

-- Generated from ChapterSirkWhitening.lean — solution of BookProof.ChapterSirkWhitening.rangeProj_eq_of_range_eq
import Mathlib
import Definitions.Def_ChapterSirkWhitening
import Theorems.Thm_BookProof_ChapterSirkWhitening_rangeProj_adjoint
import Theorems.Thm_BookProof_ChapterSirkWhitening_rangeProj_comp_of_le
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
    (h12 : ∀ y : F, ∃ z : G, V₁ y = V₂ z)
    (h21 : ∀ z : G, ∃ y : F, V₂ z = V₁ y) :
    rangeProj V₁ = rangeProj V₂ := by

  have hP21 : (rangeProj V₂).comp (rangeProj V₁) = rangeProj V₁ :=
    rangeProj_comp_of_le V₁ V₂ hV₂ h12
  have hP12 : (rangeProj V₁).comp (rangeProj V₂) = rangeProj V₂ :=
    rangeProj_comp_of_le V₂ V₁ hV₁ h21
  have hadj : ContinuousLinearMap.adjoint ((rangeProj V₂).comp (rangeProj V₁))
      = (rangeProj V₁).comp (rangeProj V₂) := by
    rw [ContinuousLinearMap.adjoint_comp, rangeProj_adjoint V₁, rangeProj_adjoint V₂]
  calc rangeProj V₁ = ContinuousLinearMap.adjoint (rangeProj V₁) := (rangeProj_adjoint V₁).symm
    _ = ContinuousLinearMap.adjoint ((rangeProj V₂).comp (rangeProj V₁)) := by rw [hP21]
    _ = (rangeProj V₁).comp (rangeProj V₂) := hadj
    _ = rangeProj V₂ := hP12
