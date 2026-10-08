-- Prove2me | solution 1 for BookProof.ChapterA4f.no_tachyon
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:08:23.496986+00:00
-- url     : https://prove2.me/submissions/68790e7e-9bcf-4432-8841-0c24d05a6972

-- Generated from ChapterA4f.lean — theorem BookProof.ChapterA4f.no_tachyon
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4f
import Definitions.Def_ChapterA5
open BookProof.ChapterA5
open BookProof.ChapterA4f


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3 BookProof.ChapterA5

theorem solution (p : Fin 3 → ℝ) (m₁ m₂ : ℝ) :
    energySymbolR p m₁ m₂ * energySymbolR p m₁ m₂
      = ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 - (m₁ ^ 2 + m₂ ^ 2)) •
          (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [energySymbolR, coeffBoostR, coeffMass1R, coeffMass2R, coeffBoostZ,
      coeffMass1Z, coeffMass2Z, spatialIdx, mgammaZ, mgamma5Z, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply,
      RingHom.mapMatrix_apply] <;> ring

#print axioms solution

