-- Prove2me | solution 1 for BookProof.ChapterH9.spectrum_compress_subset_numRange_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T10:24:27.157054+00:00
-- url     : https://prove2.me/submissions/8b06dbed-f317-4211-abf5-30bc55d64007

import Definitions.Def_ChapterH9
import Theorems.Thm_BookProof_ChapterH9_coordIncl_norm_map
import Theorems.Thm_BookProof_ChapterH9_orthonormalEmbedding_norm_map
import Theorems.Thm_BookProof_ChapterH9_spectrum_compress_subset_numRange_compress
import Theorems.Thm_BookProof_ChapterH9_spectrum_compress_subset_numRange

noncomputable section
open BookProof.ChapterH1 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH8 BookProof.ChapterH9
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
    spectrum ℂ ((compress (orthonormalEmbedding w hw) X :
        EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)))
      ⊆ numRange (compress (orthonormalEmbedding w' hw') X)
      ∩ numRange X := by
  have hfactor := NestedEmbeddingProof.factorization hmn w w' hw hw' hnest
  have hfine := BookProof.ChapterH9.spectrum_compress_subset_numRange_compress
    (orthonormalEmbedding w hw) (orthonormalEmbedding w' hw') (coordIncl hmn) X
    hfactor (BookProof.ChapterH9.coordIncl_norm_map hmn)
  have hfull := BookProof.ChapterH9.spectrum_compress_subset_numRange
    (orthonormalEmbedding w hw) X
    (BookProof.ChapterH9.orthonormalEmbedding_norm_map w hw)
  intro z hz
  exact ⟨hfine hz, hfull hz⟩
