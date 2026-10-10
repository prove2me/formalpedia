-- Prove2me | solution 1 for BookProof.ChapterPauliLorentz.det_hermMat
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:44.379077+00:00
-- url     : https://prove2.me/submissions/6527cb8a-4a2f-4b37-b454-5fb88f9a6346

-- Generated from ChapterPauliLorentz.lean — solution of BookProof.ChapterPauliLorentz.det_hermMat
import Mathlib
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz



open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (x : Fin 4 → ℝ) : (hermMat x).det = (mink x : ℂ) := by

  simp only [hermMat, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, mink]
  push_cast
  linear_combination (x 2 : ℂ) ^ 2 * Complex.I_sq
