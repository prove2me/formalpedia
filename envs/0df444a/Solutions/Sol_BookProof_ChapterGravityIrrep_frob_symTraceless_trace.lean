-- Prove2me | solution 1 for BookProof.ChapterGravityIrrep.frob_symTraceless_trace
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:51:53.620987+00:00
-- url     : https://prove2.me/submissions/8e6d694c-2741-4274-be31-fc4988d80546

-- Generated from ChapterGravityIrrep.lean — solution of BookProof.ChapterGravityIrrep.frob_symTraceless_trace
import Mathlib
import Definitions.Def_ChapterGravityIrrep
open BookProof.ChapterGravityIrrep




open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (M : Matrix (Fin 3) (Fin 3) ℝ) :
    frobInner (symTracelessPart M) ((M.trace) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 0 := by

  simp only [frobInner, symTracelessPart, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.transpose_apply, Matrix.one_apply, smul_eq_mul, Matrix.trace,
    Matrix.diag, Fin.sum_univ_three]
  norm_num [Fin.ext_iff]
  ring
