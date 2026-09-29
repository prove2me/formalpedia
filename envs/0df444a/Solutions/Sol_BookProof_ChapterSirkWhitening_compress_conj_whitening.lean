-- Prove2me | solution 1 for BookProof.ChapterSirkWhitening.compress_conj_whitening
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T04:10:01.770307+00:00
-- url     : https://prove2.me/submissions/029427f6-6ec0-43f7-a5e4-486759c07b3d

-- Generated from ChapterSirkWhitening.lean — solution of BookProof.ChapterSirkWhitening.compress_conj_whitening
import Mathlib
import Definitions.Def_ChapterSirkWhitening
import Theorems.Thm_BookProof_ChapterSirkWhitening_adjoint_comp_rangeProj
import Theorems.Thm_BookProof_ChapterSirkWhitening_embedding_comp_whiteningEquiv
open BookProof.ChapterSirkWhitening








noncomputable section


open BookProof.ChapterH4

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

set_option maxHeartbeats 1000000 in
theorem solution (V₁ : F →L[ℂ] E) (V₂ : G →L[ℂ] E) (X : E →L[ℂ] E)
    (hV₂ : V₂.adjoint.comp V₂ = ContinuousLinearMap.id ℂ G)
    (h12 : ∀ y : F, ∃ z : G, V₁ y = V₂ z) :
    compress V₁ X
      = (whiteningEquiv V₂ V₁).comp ((compress V₂ X).comp (whiteningEquiv V₁ V₂)) := by

  have hproj := adjoint_comp_rangeProj V₁ V₂ hV₂ h12
  ext y
  have hy : V₂ (whiteningEquiv V₁ V₂ y) = V₁ y :=
    embedding_comp_whiteningEquiv V₁ V₂ hV₂ h12 y
  have hstep : V₁.adjoint (rangeProj V₂ (X (V₁ y))) = V₁.adjoint (X (V₁ y)) :=
    congrArg (fun f : E →L[ℂ] F => f (X (V₁ y))) hproj
  change V₁.adjoint (X (V₁ y))
    = V₁.adjoint (V₂ (V₂.adjoint (X (V₂ (whiteningEquiv V₁ V₂ y)))))
  rw [hy]
  exact hstep.symm
