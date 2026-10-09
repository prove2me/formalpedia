-- Prove2me | solution 1 for BookProof.ChapterA3.dgamma_clifford
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:03:36.351904+00:00
-- url     : https://prove2.me/submissions/a6be337f-913c-40cc-af81-8ca27c56cc5f

-- Generated from ChapterA3.lean — solution of BookProof.ChapterA3.dgamma_clifford
import Mathlib
import Definitions.Def_ChapterA3
import Theorems.Thm_BookProof_ChapterA3_mgamma_clifford
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (μ ν : Fin 4) :
    dgamma μ * dgamma ν + dgamma ν * dgamma μ =
      (2 * minkowski μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by

  simp only [dgamma, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← smul_add, neg_mul_neg, Complex.I_mul_I, mgamma_clifford, smul_smul]
  congr 1
  ring
