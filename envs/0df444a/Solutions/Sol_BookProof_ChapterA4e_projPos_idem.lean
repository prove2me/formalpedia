-- Prove2me | solution 1 for BookProof.ChapterA4e.projPos_idem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T04:46:22.222525+00:00
-- url     : https://prove2.me/submissions/fde7c01c-5937-48e6-ac77-11225d1916e5

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4e

open BookProof.ChapterA4e BookProof.ChapterA3 BookProof.ChapterA5 Matrix Complex

theorem solution : projPos * projPos = projPos := by
  have hZ : mgammaZ 0 * mgammaZ 0 = (-1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    decide
  have hE : enSign * enSign = -1 := by
    simp only [enSign, coeffMass1Z, ← map_mul, hZ, map_neg, map_one]
  have hX : (I • enSign) * (I • enSign) = 1 := by
    rw [smul_mul_smul, hE, I_mul_I]
    simp [neg_smul, neg_neg, one_smul]
  have hnn : (-(I • enSign)) * -(I • enSign) = 1 := by
    rw [neg_mul_neg, hX]
  have hblock : (1 + -(I • enSign)) * (1 + -(I • enSign)) =
      (2 : ℂ) • (1 + -(I • enSign)) := by
    rw [two_smul]
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, hnn]
    ac_rfl
  rw [projPos, sub_eq_add_neg, smul_mul_smul, hblock, smul_smul]
  congr 1
  ring
