-- Prove2me | solution 1 for BookProof.ChapterGravityIrrep.irrep_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:22:59.982548+00:00
-- url     : https://prove2.me/submissions/306e9af3-0f90-4727-a40e-99e39f71eb65

-- Generated from ChapterGravityIrrep.lean — solution of BookProof.ChapterGravityIrrep.irrep_reconstruction
import Mathlib
import Definitions.Def_ChapterGravityIrrep
open BookProof.ChapterGravityIrrep




open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (1 / 2 : ℝ) • symTracelessPart M + (1 / 2 : ℝ) • antisymPart M
      + (1 / 3 : ℝ) • (M.trace) • (1 : Matrix (Fin 3) (Fin 3) ℝ) = M := by

  ext i j
  simp only [symTracelessPart, antisymPart, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
  ring
