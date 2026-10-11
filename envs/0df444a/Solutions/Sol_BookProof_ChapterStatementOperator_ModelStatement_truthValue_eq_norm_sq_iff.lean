-- Prove2me | solution 1 for BookProof.ChapterStatementOperator.ModelStatement.truthValue_eq_norm_sq_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:59:21.23216+00:00
-- url     : https://prove2.me/submissions/5e048562-692c-4ec5-8965-e0c7b194dac2

-- Generated from ChapterStatementOperator.lean — solution of BookProof.ChapterStatementOperator.ModelStatement.truthValue_eq_norm_sq_iff
import Mathlib
import Definitions.Def_ChapterStatementOperator
open BookProof.ChapterStatementOperator
open BookProof.ChapterStatementOperator.ModelStatement




open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : ModelStatement H) (ψ : H)

set_option maxHeartbeats 1000000 in
theorem solution : S.truthValue ψ = ‖ψ‖ ^ 2 ↔ S.op ψ = ψ := by

  constructor
  · intro h
    have hre : RCLike.re (inner ℂ ψ (S.op ψ)) = ‖S.op ψ‖ ^ 2 := S.truthValue_eq_norm_sq ψ
    have hsq : ‖S.op ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by rw [← S.truthValue_eq_norm_sq ψ, h]
    have hz : ‖ψ - S.op ψ‖ ^ 2 = 0 := by
      rw [norm_sub_sq (𝕜 := ℂ), hre, hsq]; ring
    have hzero : ψ - S.op ψ = 0 :=
      norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz)
    exact (sub_eq_zero.mp hzero).symm
  · intro h; rw [S.truthValue_eq_norm_sq, h]
