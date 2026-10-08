-- Prove2me | solution 1 for BookProof.ChapterA3k.projSum
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:11:29.059689+00:00
-- url     : https://prove2.me/submissions/95138f4b-cd2c-4078-ad8d-5ee1d8cf4d50

-- Generated from ChapterA3k.lean — theorem BookProof.ChapterA3k.projSum
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA3k
import Definitions.Def_ChapterA3j
open BookProof.ChapterA3j
open BookProof.ChapterA3k


open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j

private theorem projector_sum : projChirL + projChirR = 1 := by
  have h : (1 - Complex.I • chir) + (1 + Complex.I • chir) =
      (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    simp only [two_smul]
    abel
  unfold projChirL projChirR
  rw [← smul_add, h, smul_smul]
  norm_num

theorem solution : projLL + projLR + projRL + projRR = 1 := by
  calc
    _ = (projChirL + projChirR) ⊗ₖ (projChirL + projChirR) := by
      simp only [projLL, projLR, projRL, projRR, Matrix.add_kronecker, Matrix.kronecker_add]
      abel
    _ = 1 := by rw [projector_sum, Matrix.one_kronecker_one]

#print axioms solution
