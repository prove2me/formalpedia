-- Prove2me | solution 1 for BookProof.ChapterH9.numRange_compress_orthonormal_mono
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T10:18:09.594+00:00
-- url     : https://prove2.me/submissions/b62647d2-6c14-4070-a716-632370cbd7ce

import Definitions.Def_ChapterH9
import Theorems.Thm_BookProof_ChapterH9_numRange_compress_mono
import Theorems.Thm_BookProof_ChapterH9_coordIncl_norm_map

set_option autoImplicit false
noncomputable section
open BookProof.ChapterH9 BookProof.ChapterH8 BookProof.ChapterH6
open BookProof.ChapterH1 BookProof.ChapterH4 BookProof.ChapterH5
open ContinuousLinearMap

namespace NestedEmbeddingProof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private lemma embedding_linearMap {k : ℕ} (u : Fin k → E) (hu : Orthonormal ℂ u) :
    (orthonormalEmbedding u hu).toLinearMap =
      ((EuclideanSpace.basisFun (Fin k) ℂ).toBasis.constr ℂ) u := by
  rfl

private lemma embedding_basis {k : ℕ} (u : Fin k → E) (hu : Orthonormal ℂ u)
    (i : Fin k) :
    orthonormalEmbedding u hu ((EuclideanSpace.basisFun (Fin k) ℂ).toBasis i) = u i := by
  change (orthonormalEmbedding u hu).toLinearMap
    ((EuclideanSpace.basisFun (Fin k) ℂ).toBasis i) = u i
  rw [embedding_linearMap]
  exact (EuclideanSpace.basisFun (Fin k) ℂ).toBasis.constr_basis ℂ u i

private lemma inclusion_basis {m n : ℕ} (hmn : m ≤ n) (i : Fin m) :
    coordIncl hmn ((EuclideanSpace.basisFun (Fin m) ℂ).toBasis i) =
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (Fin.castLE hmn i) := by
  unfold coordIncl
  rw [embedding_basis]
  change EuclideanSpace.single (Fin.castLE hmn i) (1 : ℂ) =
    EuclideanSpace.basisFun (Fin n) ℂ (Fin.castLE hmn i)
  simp only [EuclideanSpace.basisFun_apply]

lemma factorization {m n : ℕ} (hmn : m ≤ n)
    (w : Fin m → E) (w' : Fin n → E)
    (hw : Orthonormal ℂ w) (hw' : Orthonormal ℂ w')
    (hnest : ∀ i : Fin m, w i = w' (Fin.castLE hmn i)) :
    orthonormalEmbedding w hw = (orthonormalEmbedding w' hw').comp (coordIncl hmn) := by
  have hlin : (orthonormalEmbedding w hw).toLinearMap =
      ((orthonormalEmbedding w' hw').comp (coordIncl hmn)).toLinearMap := by
    apply (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ext
    intro i
    change orthonormalEmbedding w hw ((EuclideanSpace.basisFun (Fin m) ℂ).toBasis i) =
      orthonormalEmbedding w' hw'
        (coordIncl hmn ((EuclideanSpace.basisFun (Fin m) ℂ).toBasis i))
    rw [embedding_basis, inclusion_basis, embedding_basis]
    exact hnest i
  ext x
  exact LinearMap.congr_fun hlin x

end NestedEmbeddingProof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem solution {m n : ℕ} (hmn : m ≤ n) (X : E →L[ℂ] E)
    (w : Fin m → E) (w' : Fin n → E) (hw : Orthonormal ℂ w) (hw' : Orthonormal ℂ w')
    (hnest : ∀ i : Fin m, w i = w' (Fin.castLE hmn i)) :
    numRange (compress (orthonormalEmbedding w hw) X)
      ⊆ numRange (compress (orthonormalEmbedding w' hw') X) := by
  exact BookProof.ChapterH9.numRange_compress_mono
    (orthonormalEmbedding w hw) (orthonormalEmbedding w' hw') (coordIncl hmn) X
    (NestedEmbeddingProof.factorization hmn w w' hw hw' hnest)
    (BookProof.ChapterH9.coordIncl_norm_map hmn)

#print axioms solution
