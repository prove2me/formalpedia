-- Prove2me | solution 1 for BookProof.ChapterH8.sirk_band_refinement_krylov
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T23:04:51.294334+00:00
-- url     : https://prove2.me/submissions/3d3dde40-515e-4514-b763-630a8f318bd8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterH8Bases.lean — solution of BookProof.ChapterH8.sirk_band_refinement_krylov
import Mathlib
import Definitions.Def_ChapterH8Bases
import Theorems.Thm_BookProof_ChapterH8_sirk_band_refinement_of_orthonormal
import Theorems.Thm_BookProof_ChapterH8_krylov_li_of_le
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH8
open BookProof.ChapterH8



noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {m n : ℕ} (hmn : m ≤ n) (H : E →ₗ[ℂ] E) (v : E)
    (X : E →L[ℂ] E) (hli : LinearIndependent ℂ (fun i : Fin n => (H ^ (i : ℕ)) v))
    (hinvm : ∀ x : EuclideanSpace ℂ (Fin m), ∃ y : EuclideanSpace ℂ (Fin m),
      X (krylovEmbedding H v (krylov_li_of_le hmn hli) x)
        = krylovEmbedding H v (krylov_li_of_le hmn hli) y)
    (hinvn : ∀ x : EuclideanSpace ℂ (Fin n), ∃ y : EuclideanSpace ℂ (Fin n),
      X (krylovEmbedding H v hli x) = krylovEmbedding H v hli y)
    (p : Polynomial ℂ) (u : E)
    (hu : krylovEmbedding H v (krylov_li_of_le hmn hli)
      ((adjoint (krylovEmbedding H v (krylov_li_of_le hmn hli))) u) = u) :
    krylovEmbedding H v hli
        ((Polynomial.aeval (compress (krylovEmbedding H v hli) X) p)
          ((adjoint (krylovEmbedding H v hli)) u))
      = krylovEmbedding H v (krylov_li_of_le hmn hli)
        ((Polynomial.aeval (compress (krylovEmbedding H v (krylov_li_of_le hmn hli)) X) p)
          ((adjoint (krylovEmbedding H v (krylov_li_of_le hmn hli))) u)) :=
  sirk_band_refinement_of_orthonormal hmn X
      (fun i : Fin m => krylovOrthonormalSeq H v (i : ℕ))
      (fun i : Fin n => krylovOrthonormalSeq H v (i : ℕ))
      (krylovOrthonormal_orthonormal H v (krylov_li_of_le hmn hli))
      (krylovOrthonormal_orthonormal H v hli)
      (fun _ => rfl) hinvm hinvn p u hu
