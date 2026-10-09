-- Prove2me | solution 1 for BookProof.ChapterA3.upsilonC_metric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:34:15.00591+00:00
-- url     : https://prove2.me/submissions/11cc0e52-1c5d-40fa-baff-7f015daf67db

-- Generated from ChapterA3h.lean — solution of BookProof.ChapterA3.upsilonC_metric
import Mathlib
import Definitions.Def_ChapterA3h
import Theorems.Thm_BookProof_ChapterA3_upsilonC_Qc
import Theorems.Thm_BookProof_ChapterA3_bilC_ext
import Theorems.Thm_BookProof_ChapterA3_bilC_minkowski
import Theorems.Thm_BookProof_ChapterA3_bilC_conj
import Theorems.Thm_BookProof_ChapterA3_toC_minkowski_symm
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.det = 1) :
    (UpsilonC T)ᵀ * toC minkowskiMat * UpsilonC T = toC minkowskiMat := by

  apply bilC_ext
  · -- symmetry of the left side
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      toC_minkowski_symm, ← Matrix.mul_assoc]
  · exact toC_minkowski_symm
  · intro x
    rw [bilC_conj, bilC_minkowski, bilC_minkowski, upsilonC_Qc T hT]
