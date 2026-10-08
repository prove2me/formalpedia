-- Prove2me | solution 1 for BookProof.ChapterA4f.boostZ_scales_translation
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:08:19.617436+00:00
-- url     : https://prove2.me/submissions/b12cdd95-8a11-4b00-b7ec-2c4b8d6b557f

-- Generated from ChapterA4f.lean — theorem BookProof.ChapterA4f.boostZ_scales_translation
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4f
open BookProof.ChapterA4f


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3 BookProof.ChapterA5

theorem solution (l : ℂ) (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (boostZ l * T * boostZ l⁻¹) 1 0 = (l⁻¹) ^ 2 * T 1 0 := by
  simp [boostZ, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring

#print axioms solution
