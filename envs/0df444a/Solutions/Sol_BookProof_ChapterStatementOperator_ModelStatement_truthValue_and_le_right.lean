-- Prove2me | solution 1 for BookProof.ChapterStatementOperator.ModelStatement.truthValue_and_le_right
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:13:09.856371+00:00
-- url     : https://prove2.me/submissions/333ef282-5fa9-49f8-b44b-c3b97e6f993d

-- Generated from ChapterStatementOperator.lean — solution of BookProof.ChapterStatementOperator.ModelStatement.truthValue_and_le_right
import Mathlib
import Definitions.Def_ChapterStatementOperator
import Definitions.Def_ChapterSirkGroupTransfer
open BookProof.ChapterStatementOperator
open BookProof.ChapterStatementOperator.ModelStatement




open ContinuousLinearMap
open BookProof.ChapterSirkGroupTransfer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : ModelStatement H) (ψ : H)


@[simp] private theorem and_op (S T : ModelStatement H) (hcomm : S.op ∘L T.op = T.op ∘L S.op) :
    (S.and T hcomm).op = S.op ∘L T.op := rfl

set_option maxHeartbeats 1000000 in
theorem solution (S T : ModelStatement H)
    (hcomm : S.op ∘L T.op = T.op ∘L S.op) :
    (S.and T hcomm).truthValue ψ ≤ T.truthValue ψ := by

  rw [truthValue_eq_norm_sq, truthValue_eq_norm_sq, and_op]
  have hle : ‖S.op (T.op ψ)‖ ≤ ‖T.op ψ‖ := S.norm_op_le (T.op ψ)
  simpa using pow_le_pow_left₀ (norm_nonneg (S.op (T.op ψ))) hle 2
