-- Prove2me | solution 1 for BookProof.ChapterH8.orthonormalEmbedding_nested
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:57:21.049793+00:00
-- url     : https://prove2.me/submissions/8fcfd0be-8abe-467f-a628-8384c53bd21c

import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH8Bases
import Definitions.Def_ChapterH8
-- Generated from ChapterH8Bases.lean — theorem BookProof.ChapterH8.orthonormalEmbedding_nested
open BookProof.ChapterH8


noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ContinuousLinearMap
theorem solution {m n : ℕ} (hmn : m ≤ n)
    (w : Fin m → E) (w' : Fin n → E) (hw : Orthonormal ℂ w) (hw' : Orthonormal ℂ w')
    (hnest : ∀ i : Fin m, w i = w' (Fin.castLE hmn i)) :
    orthonormalEmbedding w hw = (orthonormalEmbedding w' hw').comp (coordIncl hmn) := by
  have hbasis : ∀ {k : ℕ} (u : Fin k → E) (hu : Orthonormal ℂ u) (i : Fin k),
      orthonormalEmbedding u hu (EuclideanSpace.single i (1 : ℂ)) = u i := by
    intro k u hu i
    have : (EuclideanSpace.single i (1 : ℂ)) = (EuclideanSpace.basisFun (Fin k) ℂ).toBasis i := by
      simp
    rw [this]
    show ((EuclideanSpace.basisFun (Fin k) ℂ).toBasis.constr ℂ u) _ = u i
    exact Module.Basis.constr_basis _ _ _ _
  have hbasis2 : ∀ (u : Fin m → EuclideanSpace ℂ (Fin n)) (hu : Orthonormal ℂ u) (i : Fin m),
      orthonormalEmbedding u hu (EuclideanSpace.single i (1 : ℂ)) = u i := by
    intro u hu i
    have : (EuclideanSpace.single i (1 : ℂ)) = (EuclideanSpace.basisFun (Fin m) ℂ).toBasis i := by
      simp
    rw [this]
    show ((EuclideanSpace.basisFun (Fin m) ℂ).toBasis.constr ℂ u) _ = u i
    exact Module.Basis.constr_basis _ _ _ _
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply]
  rw [hbasis, coordIncl, hbasis2, hbasis, hnest]
