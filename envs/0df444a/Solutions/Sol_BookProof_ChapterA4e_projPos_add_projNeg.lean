-- Prove2me | solution 1 for BookProof.ChapterA4e.projPos_add_projNeg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T04:32:16.355673+00:00
-- url     : https://prove2.me/submissions/202da41f-8e76-426b-9c88-853d3583609b

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4e

open BookProof.ChapterA4e BookProof.ChapterA3 BookProof.ChapterA5 Matrix Complex

theorem solution : projPos + projNeg = 1 := by
  simp only [projPos, projNeg, sub_eq_add_neg, ← smul_add]
  have hsum : (1 + -(I • enSign)) + (1 + I • enSign) =
      (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    calc
      (1 + -(I • enSign)) + (1 + I • enSign)
          = (1 + 1) + (-(I • enSign) + I • enSign) := by abel
      _ = (1 + 1) := by simp
      _ = (2 : ℂ) • 1 := by simp [two_smul]
  rw [hsum, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
