-- Prove2me | solution 1 for BookProof.ChapterA3.upsilonC_nullCol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:52:17.295055+00:00
-- url     : https://prove2.me/submissions/564c6fe0-d8cd-4122-8ebe-204c9f74d536

-- Generated from ChapterA4d.lean — solution of BookProof.ChapterA3.upsilonC_nullCol
import Mathlib
import Definitions.Def_ChapterA4d
import Theorems.Thm_BookProof_ChapterA3_pauliCoeff_add
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ) (μ : Fin 4) :
    UpsilonC T μ 0 + UpsilonC T μ 3 = pauliCoeff (Tᴴ * (pauliσ 0 + pauliσ 3) * T) μ := by

  unfold UpsilonC
  simp only [Matrix.of_apply]
  rw [← pauliCoeff_add]
  congr 1
  simp [Matrix.mul_add, Matrix.add_mul]
