-- Prove2me | solution 1 for BookProof.ChapterA3.dgamma_commutant_scalar
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:12:57.171991+00:00
-- url     : https://prove2.me/submissions/42f9fb89-0d60-4cd9-8624-a82773587450

-- Generated from ChapterPauliCommutant.lean — solution of BookProof.ChapterA3.dgamma_commutant_scalar
import Mathlib
import Definitions.Def_ChapterPauliCommutant
import Theorems.Thm_BookProof_ChapterA3_mgamma_commutant_scalar
import Definitions.Def_ChapterA3
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (M : Matrix (Fin 4) (Fin 4) ℂ)
    (h : ∀ μ, M * dgamma μ = dgamma μ * M) :
    M = M 0 0 • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by

  refine mgamma_commutant_scalar M fun μ => ?_
  have hI : (-Complex.I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  have := h μ
  rw [dgamma, Matrix.mul_smul, Matrix.smul_mul] at this
  exact smul_right_injective _ hI this
