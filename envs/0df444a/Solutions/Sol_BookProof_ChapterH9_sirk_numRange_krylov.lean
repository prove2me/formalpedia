-- Prove2me | solution 1 for BookProof.ChapterH9.sirk_numRange_krylov
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T22:29:30.773725+00:00
-- url     : https://prove2.me/submissions/1f881140-141e-4e41-ae99-503b2cabc8be

-- Generated from ChapterH9.lean — solution of BookProof.ChapterH9.sirk_numRange_krylov
import Mathlib
import Definitions.Def_ChapterH9
import Theorems.Thm_BookProof_ChapterH9_numRange_compress_subset
import Theorems.Thm_BookProof_ChapterH9_orthonormalEmbedding_norm_map
import Theorems.Thm_BookProof_ChapterH9_numRange_compress_orthonormal_mono
import Theorems.Thm_BookProof_ChapterH8_krylov_li_of_le
open BookProof.ChapterH9



noncomputable section


open BookProof.ChapterH1 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH8
open ContinuousLinearMap


variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {m n : ℕ} (hmn : m ≤ n) (H : E →ₗ[ℂ] E) (v : E)
    (X : E →L[ℂ] E) (hli : LinearIndependent ℂ (fun i : Fin n => (H ^ (i : ℕ)) v)) :
    numRange (compress (krylovEmbedding H v (krylov_li_of_le hmn hli)) X)
        ⊆ numRange (compress (krylovEmbedding H v hli) X)
      ∧ numRange (compress (krylovEmbedding H v hli) X) ⊆ numRange X := by

  refine ⟨numRange_compress_orthonormal_mono hmn X _ _
    (krylovOrthonormal_orthonormal H v (krylov_li_of_le hmn hli))
    (krylovOrthonormal_orthonormal H v hli)
    (fun i => by simp) , ?_⟩
  exact numRange_compress_subset _ X (orthonormalEmbedding_norm_map _ _)
