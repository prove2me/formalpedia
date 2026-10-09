-- Prove2me | solution 1 for BookProof.ChapterGravityIrrep.trace_symTracelessPart
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:51:27.588092+00:00
-- url     : https://prove2.me/submissions/3c8bdf84-3f0d-44fc-bf2b-ec13995cd6fa

-- Generated from ChapterGravityIrrep.lean — solution of BookProof.ChapterGravityIrrep.trace_symTracelessPart
import Mathlib
import Definitions.Def_ChapterGravityIrrep
open BookProof.ChapterGravityIrrep




open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (symTracelessPart M).trace = 0 := by

  simp [symTracelessPart, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  ring
