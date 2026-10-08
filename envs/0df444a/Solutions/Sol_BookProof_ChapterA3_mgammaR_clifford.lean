-- Prove2me | solution 1 for BookProof.ChapterA3.mgammaR_clifford
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T16:22:26.058978+00:00
-- url     : https://prove2.me/submissions/734551d9-bdd0-4137-a505-a51677a6cc5c

import Mathlib
import Definitions.Def_ChapterA3c
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3b

open BookProof.ChapterA3
open Matrix

private theorem mgammaZ_clifford (μ ν : Fin 4) :
    mgammaZ μ * mgammaZ ν + mgammaZ ν * mgammaZ μ =
      (-2 * minkowskiZ μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  fin_cases μ <;> fin_cases ν <;> decide

theorem solution : IsCliffordR mgammaR := by
  intro μ ν
  have hZ := mgammaZ_clifford μ ν
  have hscalar :
      (Int.castRingHom ℝ).mapMatrix ((-2 * minkowskiZ μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) =
        (-2 * minkowskiR μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext i j
    simp [minkowskiR, Matrix.one_apply, Matrix.mul_apply,
      Matrix.intCast_apply, Matrix.natCast_apply, Matrix.ofNat_apply] <;>
      split_ifs <;> ring
  have hCast := congrArg (Int.castRingHom ℝ).mapMatrix hZ
  rw [(Int.castRingHom ℝ).mapMatrix.map_add,
    (Int.castRingHom ℝ).mapMatrix.map_mul,
    (Int.castRingHom ℝ).mapMatrix.map_mul] at hCast
  rw [hscalar] at hCast
  simpa [mgammaR, minkowskiR] using hCast

#print axioms solution
