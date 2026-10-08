-- Prove2me | solution 1 for BookProof.ChapterA4e.projNeg_idem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T04:46:22.981781+00:00
-- url     : https://prove2.me/submissions/24e0b136-5f95-4cce-aac8-5be852fdacbe

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4e

open BookProof.ChapterA4e BookProof.ChapterA3 BookProof.ChapterA5 Matrix Complex

theorem solution : projNeg * projNeg = projNeg := by
  have hZ : mgammaZ 0 * mgammaZ 0 = (-1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    decide
  have hE : enSign * enSign = -1 := by
    simp only [enSign, coeffMass1Z, ← map_mul, hZ, map_neg, map_one]
  have hX : (I • enSign) * (I • enSign) = 1 := by
    rw [smul_mul_smul, hE, I_mul_I]
    simp [neg_smul, neg_neg, one_smul]
  have hblock : (1 + I • enSign) * (1 + I • enSign) = (2 : ℂ) • (1 + I • enSign) := by
    rw [two_smul]
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, hX]
    ac_rfl
  rw [projNeg, smul_mul_smul, hblock, smul_smul]
  congr 1
  ring
