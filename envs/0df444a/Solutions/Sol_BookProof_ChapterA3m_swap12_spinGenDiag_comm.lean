-- Prove2me | solution 1 for BookProof.ChapterA3m.swap12_spinGenDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:42:04.555676+00:00
-- url     : https://prove2.me/submissions/4d106beb-cd11-4619-99be-62967623c202

-- Generated from ChapterA3m.lean — solution of BookProof.ChapterA3m.swap12_spinGenDiag_comm
import Mathlib
import Definitions.Def_ChapterA3m
import Theorems.Thm_BookProof_ChapterA3m_swap12_kronecker
open BookProof.ChapterA3m



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3l

set_option maxHeartbeats 1000000 in
theorem solution (μ ν : Fin 4) :
    swap12 * spinGenDiag3 μ ν = spinGenDiag3 μ ν * swap12 := by

  -- Applying the identity for `swap12` to each term in `spinGenDiag3`.
  have step1 : ∀ (μ ν : Fin 4),    (swap12 * (spinGen μ ν ⊗ₖ 1) ⊗ₖ 1 = ((1 ⊗ₖ spinGen μ ν) ⊗ₖ 1) *
      swap12) := by
    intro μ ν;
    convert swap12_kronecker ( spinGen μ ν ) 1 1 using 1;
  convert congr_arg₂ ( fun x y => x + y ) ( congr_arg₂ ( fun x y => x + y ) ( step1 μ ν ) (
      swap12_kronecker ( 1 : Matrix ( Fin 4 ) ( Fin 4 ) ℂ ) ( spinGen μ ν ) ( 1 : Matrix ( Fin 4 ) (
          Fin 4 ) ℂ ) ) ) ( swap12_kronecker ( 1 : Matrix ( Fin 4 ) ( Fin 4 ) ℂ ) ( 1 : Matrix ( Fin
              4 ) ( Fin 4 ) ℂ ) ( spinGen μ ν ) ) using 1;
  · unfold spinGenDiag3; simp [ Matrix.mul_add ] ;
  · unfold spinGenDiag3; simp only [zero_mul, implies_true, mul_zero, mul_one, kroneckerMap_one_one,
      add_assoc, add_mul] ;
    abel1
