-- Prove2me | solution 1 for BookProof.ChapterA3n.permMat_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:48:44.396833+00:00
-- url     : https://prove2.me/submissions/ee3a7099-9a43-4676-ada2-cb6c0fd2b8b6

-- Generated from ChapterA3n.lean — solution of BookProof.ChapterA3n.permMat_mul
import Mathlib
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n



open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j

set_option maxHeartbeats 1000000 in
theorem solution {N : ℕ} (σ τ : Equiv.Perm (Fin N)) :
    permMat σ * permMat τ = permMat (σ * τ) := by

  ext a c; simp only [mul_apply] ;
  unfold permMat; simp [ Finset.sum_ite ] ;
  rfl
