-- Prove2me | solution 1 for BookProof.ChapterA3.mgamma_clifford
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:58:21.415633+00:00
-- url     : https://prove2.me/submissions/7e2277b4-59d4-4fe4-8f5d-4de8bd43053c

-- Generated from ChapterA3.lean — solution of BookProof.ChapterA3.mgamma_clifford
import Mathlib
import Definitions.Def_ChapterA3
import Theorems.Thm_BookProof_ChapterA3_mgammaZ_clifford
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (μ ν : Fin 4) :
    mgamma μ * mgamma ν + mgamma ν * mgamma μ =
      (-2 * minkowski μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by

  have h := congrArg (Int.castRingHom ℂ).mapMatrix (mgammaZ_clifford μ ν)
  rw [map_add, map_mul, map_mul, map_zsmul, map_one] at h
  rw [mgamma, mgamma, h, minkowski]
  ext i j
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, zsmul_eq_mul]
  by_cases hij : i = j <;> simp [hij]
