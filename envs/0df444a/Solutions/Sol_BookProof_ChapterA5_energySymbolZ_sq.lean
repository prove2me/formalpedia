-- Prove2me | solution 1 for BookProof.ChapterA5.energySymbolZ_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:54:57.286273+00:00
-- url     : https://prove2.me/submissions/1db52e9b-00a9-4eea-9d83-d612c0f50299

-- Generated from ChapterA5.lean — solution of BookProof.ChapterA5.energySymbolZ_sq
import Mathlib
import Definitions.Def_ChapterA5
open BookProof.ChapterA5



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin 3 → ℤ) (m₁ m₂ : ℤ) :
    energySymbolZ p m₁ m₂ * energySymbolZ p m₁ m₂
      = ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 - m₁ ^ 2 - m₂ ^ 2) •
          (1 : Matrix (Fin 4) (Fin 4) ℤ) := by

  ext i j
  simp only [energySymbolZ, coeffBoostZ, coeffMass1Z, coeffMass2Z, spatialIdx,
    mgammaZ, mgamma5Z, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.neg_apply, Matrix.one_apply, Fin.sum_univ_four, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.smul_of, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp <;> ring
