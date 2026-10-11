-- Prove2me | solution 1 for BookProof.ChapterStatementOperator.ModelStatement.truthValue_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:59:22.178512+00:00
-- url     : https://prove2.me/submissions/23d5b8f2-2f00-46c9-a02f-a9a76877df12

-- Generated from ChapterStatementOperator.lean — solution of BookProof.ChapterStatementOperator.ModelStatement.truthValue_eq_zero_iff
import Mathlib
import Definitions.Def_ChapterStatementOperator
open BookProof.ChapterStatementOperator
open BookProof.ChapterStatementOperator.ModelStatement




open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : ModelStatement H) (ψ : H)

set_option maxHeartbeats 1000000 in
theorem solution : S.truthValue ψ = 0 ↔ S.op ψ = 0 := by

  rw [S.truthValue_eq_norm_sq]
  constructor
  · intro h
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)
  · intro h; rw [h]; simp
