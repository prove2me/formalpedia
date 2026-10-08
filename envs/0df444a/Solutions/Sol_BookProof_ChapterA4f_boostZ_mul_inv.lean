-- Prove2me | solution 1 for BookProof.ChapterA4f.boostZ_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:08:16.770841+00:00
-- url     : https://prove2.me/submissions/08ff5195-2b75-4dc7-9c61-f82695a887d7

-- Generated from ChapterA4f.lean — theorem BookProof.ChapterA4f.boostZ_mul_inv
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4f
open BookProof.ChapterA4f


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3 BookProof.ChapterA5

theorem solution {l : ℂ} (hl : l ≠ 0) : boostZ l * boostZ l⁻¹ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostZ, Matrix.mul_apply, Fin.sum_univ_two, hl]

#print axioms solution

