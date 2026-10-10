-- Prove2me | solution 1 for BookProof.ChapterPauliGrover.pauliX_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:36.858179+00:00
-- url     : https://prove2.me/submissions/084bebc4-90ae-41db-8f64-684da8ee4b45

-- Generated from ChapterPauliGrover.lean — solution of BookProof.ChapterPauliGrover.pauliX_sq
import Mathlib
import Definitions.Def_ChapterPauliGrover
import Definitions.Def_ChapterConditional
open BookProof.ChapterPauliGrover



open scoped BigOperators Matrix ComplexConjugate
open Matrix
open BookProof.ChapterConditional

set_option maxHeartbeats 1000000 in
theorem solution : pauliX * pauliX = 1 := by

  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]
