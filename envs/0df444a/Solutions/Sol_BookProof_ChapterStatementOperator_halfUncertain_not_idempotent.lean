-- Prove2me | solution 1 for BookProof.ChapterStatementOperator.halfUncertain_not_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:13:21.538444+00:00
-- url     : https://prove2.me/submissions/77b799dc-be3c-4dce-9fea-9b5800d32ac6

-- Generated from ChapterStatementOperator.lean — solution of BookProof.ChapterStatementOperator.halfUncertain_not_idempotent
import Mathlib
import Definitions.Def_ChapterStatementOperator
open BookProof.ChapterStatementOperator




open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : ModelStatement H) (ψ : H)


@[simp] private theorem halfUncertain_op :
    (halfUncertain (H := H)).op = (1 / 2 : ℂ) • (1 : H →L[ℂ] H) := rfl

set_option maxHeartbeats 1000000 in
theorem solution (h : ∃ ψ : H, ψ ≠ 0) :
    ¬ ((halfUncertain (H := H)).op ∘L (halfUncertain (H := H)).op
        = (halfUncertain (H := H)).op) := by

  obtain ⟨ψ, hψ⟩ := h
  intro hcon
  rw [halfUncertain_op] at hcon
  have happ := congrArg (fun A : H →L[ℂ] H => A ψ) hcon
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_smul] at happ
  have h4 : ((1 / 2 : ℂ) * (1 / 2) - (1 / 2 : ℂ)) • ψ = 0 := by
    rw [sub_smul, sub_eq_zero]; exact happ
  rcases smul_eq_zero.mp h4 with h1 | h0
  · norm_num at h1
  · exact hψ h0
