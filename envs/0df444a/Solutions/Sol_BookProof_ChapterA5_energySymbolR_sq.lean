-- Prove2me | solution 1 for BookProof.ChapterA5.energySymbolR_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:54:58.444202+00:00
-- url     : https://prove2.me/submissions/e5f981c0-2617-45e1-b283-fc83ceb777fd

-- Generated from ChapterA5.lean — solution of BookProof.ChapterA5.energySymbolR_sq
import Mathlib
import Definitions.Def_ChapterA5
open BookProof.ChapterA5



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin 3 → ℝ) (m₁ m₂ : ℝ) :
    energySymbolR p m₁ m₂ * energySymbolR p m₁ m₂
      = ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 - m₁ ^ 2 - m₂ ^ 2) •
          (1 : Matrix (Fin 4) (Fin 4) ℝ) := by

  ext i j
  simp only [energySymbolR, coeffBoostR, coeffMass1R, coeffMass2R, coeffBoostZ,
    coeffMass1Z, coeffMass2Z, spatialIdx, mgammaZ, mgamma5Z, RingHom.mapMatrix_apply,
    Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.neg_apply, Matrix.one_apply, Fin.sum_univ_four, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, smul_eq_mul, eq_intCast, Int.cast_neg]
  fin_cases i <;> fin_cases j <;> push_cast <;> ring
