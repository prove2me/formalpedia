-- Prove2me | solution 1 for BookProof.ChapterStatementOperator.ModelStatement.truthValue_mem_unitInterval
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:59:20.334302+00:00
-- url     : https://prove2.me/submissions/9902fecf-dfac-45ac-9359-9317ac5c86ed

-- Generated from ChapterStatementOperator.lean — solution of BookProof.ChapterStatementOperator.ModelStatement.truthValue_mem_unitInterval
import Mathlib
import Definitions.Def_ChapterStatementOperator
open BookProof.ChapterStatementOperator
open BookProof.ChapterStatementOperator.ModelStatement




open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : ModelStatement H) (ψ : H)

set_option maxHeartbeats 1000000 in
theorem solution (hψ : ‖ψ‖ = 1) :
    S.truthValue ψ ∈ Set.Icc (0 : ℝ) 1 := ⟨S.truthValue_nonneg ψ, by simpa [hψ] using S.truthValue_le_norm_sq ψ⟩
