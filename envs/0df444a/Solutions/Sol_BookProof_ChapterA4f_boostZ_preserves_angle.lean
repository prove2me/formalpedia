-- Prove2me | solution 1 for BookProof.ChapterA4f.boostZ_preserves_angle
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:08:18.219204+00:00
-- url     : https://prove2.me/submissions/c44b5201-9632-4cdf-8af9-67ba0ed5174e

-- Generated from ChapterA4f.lean — theorem BookProof.ChapterA4f.boostZ_preserves_angle
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4f
open BookProof.ChapterA4f


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3 BookProof.ChapterA5

theorem solution {l : ℂ} (hl : l ≠ 0) (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (boostZ l * T * boostZ l⁻¹) 0 0 = T 0 0 := by
  simp [boostZ, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  field_simp

#print axioms solution
