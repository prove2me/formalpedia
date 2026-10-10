-- Prove2me | solution 1 for BookProof.ChapterParityChirality.chi_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:45.700162+00:00
-- url     : https://prove2.me/submissions/4c1e41b2-b8b0-4e6d-9049-cacd3905c374

-- Generated from ChapterParityChirality.lean — solution of BookProof.ChapterParityChirality.chi_sq
import Mathlib
import Definitions.Def_ChapterParityChirality
import Theorems.Thm_BookProof_ChapterA3_mgamma5_sq
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
theorem solution : chi * chi = 1 := by

  have hp3 : pauli3 * pauli3 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauli3, Matrix.mul_apply, Fin.sum_univ_two]
  have hp : (Complex.I • pauli3) * (Complex.I • pauli3) = -1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hp3, smul_smul, Complex.I_mul_I]
    simp
  rw [chi, ← Matrix.mul_kronecker_mul, hp, BookProof.ChapterA3.mgamma5_sq]
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [Matrix.one_apply, Matrix.kroneckerMap, Prod.ext_iff]
  by_cases h : i = k <;> by_cases h2 : j = l <;> simp [h, h2]
