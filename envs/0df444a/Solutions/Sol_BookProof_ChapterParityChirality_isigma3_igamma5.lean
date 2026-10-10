-- Prove2me | solution 1 for BookProof.ChapterParityChirality.isigma3_igamma5
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:42.988305+00:00
-- url     : https://prove2.me/submissions/e5e77cb5-459f-4eb5-9be5-fd5d3c455d0a

-- Generated from ChapterParityChirality.lean — solution of BookProof.ChapterParityChirality.isigma3_igamma5
import Mathlib
import Definitions.Def_ChapterParityChirality
import Definitions.Def_ChapterParity
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterParitySU2
open BookProof.ChapterParityChirality



open Matrix
open scoped Kronecker


open BookProof.ChapterA3
open BookProof.ChapterParity
open BookProof.ChapterParitySU2

set_option maxHeartbeats 1000000 in
theorem solution : isigma3 * igamma5 = chi := by

  convert Matrix.mul_kronecker_mul ( Complex.I • pauli3 ) 1 1 mgamma5;
  all_goals try exact ⟨ 1 ⟩;
  · ext ⟨ i, j ⟩ ⟨ k, l ⟩ ; simp only [isigma3, igamma5, mul_one, one_mul, kroneckerMap_apply,
      Matrix.smul_apply, smul_eq_mul];
    simp only [kroneckerMap, Matrix.smul_apply, smul_eq_mul, mul_apply, of_apply];
    simp only [one_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite,
        Finset.sum_const_zero, add_zero];
    rw [ Finset.sum_eq_single ( k, j ) ] <;> aesop;
  · convert Matrix.mul_kronecker_mul ( Complex.I • pauli3 ) 1 1 mgamma5;
    unfold chi; aesop;
