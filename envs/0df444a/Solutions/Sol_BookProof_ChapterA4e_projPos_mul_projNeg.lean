-- Prove2me | solution 1 for BookProof.ChapterA4e.projPos_mul_projNeg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T04:44:16.918041+00:00
-- url     : https://prove2.me/submissions/156265af-19ff-4571-a35a-376fc03401ab

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4e

open BookProof.ChapterA4e BookProof.ChapterA3 BookProof.ChapterA5 Matrix Complex

theorem solution : projPos * projNeg = 0 := by
  have hZ : mgammaZ 0 * mgammaZ 0 = (-1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    decide
  have hE : enSign * enSign = -1 := by
    simp only [enSign, coeffMass1Z, ← map_mul, hZ, map_neg, map_one]
  have hX : (I • enSign) * (I • enSign) = 1 := by
    rw [smul_mul_smul, hE, I_mul_I]
    simp [neg_smul, neg_neg, one_smul]
  have hblock : (1 + -(I • enSign)) * (1 + I • enSign) = 0 := by
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, neg_mul, hX]
    have : 1 + I • enSign + (-(I • enSign) + -1) =
        (1 + -1) + (I • enSign + -(I • enSign)) := by ac_rfl
    rw [this]
    simp
  rw [projPos, projNeg, sub_eq_add_neg, smul_mul_smul, hblock, smul_zero]
