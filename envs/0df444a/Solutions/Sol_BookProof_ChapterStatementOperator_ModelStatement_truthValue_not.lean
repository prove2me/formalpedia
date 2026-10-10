-- Prove2me | solution 1 for BookProof.ChapterStatementOperator.ModelStatement.truthValue_not
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:12:56.938246+00:00
-- url     : https://prove2.me/submissions/c8751189-db49-48e1-95b0-f1627216b2ac

-- Generated from ChapterStatementOperator.lean — solution of BookProof.ChapterStatementOperator.ModelStatement.truthValue_not
import Mathlib
import Definitions.Def_ChapterStatementOperator
open BookProof.ChapterStatementOperator
open BookProof.ChapterStatementOperator.ModelStatement




open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : ModelStatement H) (ψ : H)


@[simp] private theorem not_op : S.not.op = 1 - S.op := rfl

set_option maxHeartbeats 1000000 in
theorem solution : S.not.truthValue ψ = ‖ψ‖ ^ 2 - S.truthValue ψ := by

  simp [truthValue, not_op, inner_sub_right, ← Complex.ofReal_pow]
