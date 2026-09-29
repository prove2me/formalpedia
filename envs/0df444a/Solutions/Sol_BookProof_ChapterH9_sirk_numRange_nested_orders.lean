-- Prove2me | solution 1 for BookProof.ChapterH9.sirk_numRange_nested_orders
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T10:24:25.927335+00:00
-- url     : https://prove2.me/submissions/fdb5dd04-bfd9-4f4e-b867-01fb143ef595

import Definitions.Def_ChapterH9
import Theorems.Thm_BookProof_ChapterH9_coordIncl_norm_map
import Theorems.Thm_BookProof_ChapterH9_orthonormalEmbedding_norm_map
import Theorems.Thm_BookProof_ChapterH9_numRange_compress_mono
import Theorems.Thm_BookProof_ChapterH9_numRange_compress_subset
import Theorems.Thm_BookProof_ChapterH9_numRange_subset_closedBall
import Theorems.Thm_BookProof_ChapterH9_norm_compress_mono
import Theorems.Thm_BookProof_ChapterH9_norm_compress_le

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
    numRange (compress (orthonormalEmbedding w hw) X)
        ⊆ numRange (compress (orthonormalEmbedding w' hw') X)
      ∧ numRange (compress (orthonormalEmbedding w' hw') X) ⊆ numRange X
      ∧ numRange X ⊆ Metric.closedBall (0 : ℂ) ‖X‖
      ∧ ‖compress (orthonormalEmbedding w hw) X‖
          ≤ ‖compress (orthonormalEmbedding w' hw') X‖
      ∧ ‖compress (orthonormalEmbedding w' hw') X‖ ≤ ‖X‖ := by
  have hfactor := NestedEmbeddingProof.factorization hmn w w' hw hw' hnest
  have hJiso := BookProof.ChapterH9.coordIncl_norm_map hmn
  have hViso := BookProof.ChapterH9.orthonormalEmbedding_norm_map w' hw'
  exact ⟨BookProof.ChapterH9.numRange_compress_mono _ _ _ X hfactor hJiso,
    BookProof.ChapterH9.numRange_compress_subset _ X hViso,
    BookProof.ChapterH9.numRange_subset_closedBall X,
    BookProof.ChapterH9.norm_compress_mono _ _ _ X hfactor hJiso,
    BookProof.ChapterH9.norm_compress_le _ X hViso⟩
