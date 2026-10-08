-- Prove2me | solution 1 for BookProof.ChapterA4h.localizable_iff_massShell
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:52:08.289721+00:00
-- url     : https://prove2.me/submissions/5fb3fb4b-e9d2-4938-b29a-90c460789ffe

import Mathlib
import Definitions.Def_ChapterA4h
open Matrix BookProof.ChapterA3 BookProof.ChapterA4e BookProof.ChapterA4f BookProof.ChapterA5 BookProof.ChapterA4h
set_option maxHeartbeats 0

private lemma symbol_sq (p : Fin 3 → ℝ) (m₁ m₂ : ℝ) :
    energySymbolR p m₁ m₂ * energySymbolR p m₁ m₂ =
      (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 - (m₁ ^ 2 + m₂ ^ 2)) •
        (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [energySymbolR, coeffBoostR, coeffMass1R, coeffMass2R, coeffBoostZ,
      coeffMass1Z, coeffMass2Z, spatialIdx, mgammaZ, mgamma5Z, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply,
      RingHom.mapMatrix_apply] <;> ring

private lemma shell (p : Fin 3 → ℝ) (m₁ m₂ : ℝ) :
    Localizable p m₁ m₂ ↔ p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = m₁ ^ 2 + m₂ ^ 2 := by
  unfold Localizable
  rw [isUnit_iff_ne_zero]
  have hd := congrArg Matrix.det (symbol_sq p m₁ m₂)
  norm_num at hd
  constructor
  · intro h
    have hz : (energySymbolR p m₁ m₂).det = 0 := by simpa using h
    rw [hz] at hd
    simp only [zero_mul] at hd
    have := (pow_eq_zero_iff (by decide : 4 ≠ 0)).mp hd.symm
    linarith
  · intro h
    have hz : (energySymbolR p m₁ m₂).det = 0 := by
      have : (energySymbolR p m₁ m₂).det * (energySymbolR p m₁ m₂).det = 0 := by
        simpa [h] using hd
      exact (mul_self_eq_zero.mp this)
    simpa [hz]

theorem solution (p : Fin 3 → ℝ) (m₁ m₂ : ℝ) :
    Localizable p m₁ m₂ ↔ p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = m₁ ^ 2 + m₂ ^ 2 := by
  exact shell p m₁ m₂

#print axioms solution
