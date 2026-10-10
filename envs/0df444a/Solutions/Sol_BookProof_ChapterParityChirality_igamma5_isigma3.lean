-- Prove2me | solution 1 for BookProof.ChapterParityChirality.igamma5_isigma3
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:44.375957+00:00
-- url     : https://prove2.me/submissions/5cc19eca-f627-4729-8a5a-63a74df7b76c

-- Generated from ChapterParityChirality.lean — solution of BookProof.ChapterParityChirality.igamma5_isigma3
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
theorem solution : igamma5 * isigma3 = chi := by

  ext ⟨ i, j ⟩ ⟨ k, l ⟩ ; simp only [igamma5, isigma3, mul_apply, kroneckerMap_apply,
      Matrix.smul_apply, smul_eq_mul, chi];
  simp only [one_apply, ite_mul, one_mul, zero_mul, mul_comm, mul_left_comm, mul_ite, mul_zero,
      ite_self];
  rw [ Finset.sum_eq_single ( i, l ) ] <;> aesop
