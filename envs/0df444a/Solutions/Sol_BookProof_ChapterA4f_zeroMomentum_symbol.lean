-- Prove2me | solution 1 for BookProof.ChapterA4f.zeroMomentum_symbol
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:08:24.974989+00:00
-- url     : https://prove2.me/submissions/65bdcb45-c88e-4723-a727-58fad9fc9ab9

-- Generated from ChapterA4f.lean — theorem BookProof.ChapterA4f.zeroMomentum_symbol
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4f
import Definitions.Def_ChapterA5
open BookProof.ChapterA5
open BookProof.ChapterA4f


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3 BookProof.ChapterA5

theorem solution (m₁ m₂ : ℝ) :
    energySymbolR (fun _ => 0) m₁ m₂ * energySymbolR (fun _ => 0) m₁ m₂
      = (-(m₁ ^ 2 + m₂ ^ 2)) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [energySymbolR, coeffBoostR, coeffMass1R, coeffMass2R, coeffBoostZ,
      coeffMass1Z, coeffMass2Z, spatialIdx, mgammaZ, mgamma5Z, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply,
      RingHom.mapMatrix_apply] <;> ring

#print axioms solution

