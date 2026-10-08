-- Prove2me | solution 1 for BookProof.ChapterPauliLorentz.sigma2_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T09:05:16.138522+00:00
-- url     : https://prove2.me/submissions/06d0bffa-3b32-40c3-bc70-3045c0e3ce80

-- Generated from ChapterPauliLorentz.lean — solution of BookProof.ChapterPauliLorentz.sigma2_sq
import Mathlib
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz



open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution : σ2 * σ2 = 1 := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ2, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]
