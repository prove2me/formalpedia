-- Prove2me | solution 1 for BookProof.ChapterStatementOperator.approximate_proof_error
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:59:38.304784+00:00
-- url     : https://prove2.me/submissions/18eece36-756a-4d29-a086-ed6abd4b67c3

-- Generated from ChapterStatementOperator.lean — solution of BookProof.ChapterStatementOperator.approximate_proof_error
import Mathlib
import Definitions.Def_ChapterStatementOperator
open BookProof.ChapterStatementOperator




open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : ModelStatement H) (ψ : H)

set_option maxHeartbeats 1000000 in
theorem solution (S : ModelStatement H) (A : H →L[ℂ] H) (ε : ℝ)
    (hA : ‖A - S.op‖ ≤ ε) (ψ : H) :
    |RCLike.re (inner ℂ ψ (A ψ)) - S.truthValue ψ| ≤ ε * ‖ψ‖ ^ 2 := by

  have hdiff : RCLike.re (inner ℂ ψ (A ψ)) - S.truthValue ψ
      = RCLike.re (inner ℂ ψ ((A - S.op) ψ)) := by
    simp [ModelStatement.truthValue, inner_sub_right]
  rw [hdiff]
  have h1 := RCLike.abs_re_le_norm (inner ℂ ψ ((A - S.op) ψ))
  have h2 : ‖(inner ℂ ψ ((A - S.op) ψ) : ℂ)‖ ≤ ‖ψ‖ * ‖(A - S.op) ψ‖ := norm_inner_le_norm _ _
  have h3 : ‖(A - S.op) ψ‖ ≤ ε * ‖ψ‖ :=
    le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_right hA (norm_nonneg ψ))
  calc |RCLike.re (inner ℂ ψ ((A - S.op) ψ))| ≤ ‖ψ‖ * ‖(A - S.op) ψ‖ := le_trans h1 h2
    _ ≤ ‖ψ‖ * (ε * ‖ψ‖) := mul_le_mul_of_nonneg_left h3 (norm_nonneg ψ)
    _ = ε * ‖ψ‖ ^ 2 := by ring
