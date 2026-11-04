-- Prove2me | solution 1 for BookProof.ChapterH8.orthonormalEmbedding_range
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T21:58:17.721676+00:00
-- url     : https://prove2.me/submissions/619a5833-d3f4-4008-97c5-3aaf798f1aaf

-- Generated from ChapterH8Bases.lean — solution of BookProof.ChapterH8.orthonormalEmbedding_range
import Mathlib
import Definitions.Def_ChapterH8Bases
import Theorems.Thm_BookProof_ChapterH8_orthonormalEmbedding_single
open BookProof.ChapterH8



noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} (w : Fin m → E) (hw : Orthonormal ℂ w) :
    LinearMap.range (orthonormalEmbedding w hw : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E)
      = Submodule.span ℂ (Set.range w) := by

  have hbasis : Submodule.span ℂ (Set.range ((EuclideanSpace.basisFun (Fin m) ℂ).toBasis))
      = (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin m))) :=
    (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.span_eq
  have hcomp : ((orthonormalEmbedding w hw : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E) ∘
      ((EuclideanSpace.basisFun (Fin m) ℂ).toBasis)) = w := by
    funext i
    have hb : ((EuclideanSpace.basisFun (Fin m) ℂ).toBasis) i
        = EuclideanSpace.single i (1 : ℂ) := by
      simp [EuclideanSpace.basisFun_apply]
    simp only [Function.comp_apply, hb]
    exact orthonormalEmbedding_single w hw i
  rw [LinearMap.range_eq_map, ← hbasis, Submodule.map_span, ← Set.range_comp, hcomp]
