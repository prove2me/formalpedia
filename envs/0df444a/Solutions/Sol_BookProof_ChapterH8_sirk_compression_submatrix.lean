-- Prove2me | solution 1 for BookProof.ChapterH8.sirk_compression_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T22:48:43.970313+00:00
-- url     : https://prove2.me/submissions/49a1ed04-f8bb-4719-88af-dc5dc8557380

-- Generated from ChapterH8.lean — solution of BookProof.ChapterH8.sirk_compression_submatrix
import Mathlib
import Definitions.Def_ChapterH8
import Theorems.Thm_BookProof_ChapterH8_sirk_compression_block
open BookProof.ChapterH8



noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (X : E →L[ℂ] E)
    (Vn : EuclideanSpace ℂ (Fin n) →L[ℂ] E)
    (Vm : EuclideanSpace ℂ (Fin (n + 1)) →L[ℂ] E)
    (hnest : ∀ i : Fin n, Vn (EuclideanSpace.single i (1 : ℂ))
      = Vm (EuclideanSpace.single (Fin.castSucc i) (1 : ℂ))) :
    reduceGenerator n Vn X
      = (reduceGenerator (n + 1) Vm X).submatrix Fin.castSucc Fin.castSucc := by

  ext i j
  simpa using sirk_compression_block n X Vn Vm hnest i j
