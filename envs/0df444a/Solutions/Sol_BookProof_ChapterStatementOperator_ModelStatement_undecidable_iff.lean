-- Prove2me | solution 1 for BookProof.ChapterStatementOperator.ModelStatement.undecidable_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:59:37.256111+00:00
-- url     : https://prove2.me/submissions/315be9c8-f779-4ff5-93db-52b7d7976789

-- Generated from ChapterStatementOperator.lean — solution of BookProof.ChapterStatementOperator.ModelStatement.undecidable_iff
import Mathlib
import Definitions.Def_ChapterStatementOperator
open BookProof.ChapterStatementOperator
open BookProof.ChapterStatementOperator.ModelStatement




open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : ModelStatement H) (ψ : H)

set_option maxHeartbeats 1000000 in
theorem solution :
    S.Undecidable ↔ (∃ a : H, a ≠ 0 ∧ S.op a = a) ∧ (∃ b : H, b ≠ 0 ∧ S.op b = 0) := by

  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · obtain ⟨x, hx⟩ : ∃ x : H, S.op x ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact h0 (ContinuousLinearMap.ext hcon)
      refine ⟨S.op x, hx, ?_⟩
      rw [← ContinuousLinearMap.comp_apply, S.isIdempotent]
    · obtain ⟨x, hx⟩ : ∃ x : H, S.op x ≠ x := by
        by_contra hcon
        push_neg at hcon
        exact h1 (ContinuousLinearMap.ext (by simpa using hcon))
      refine ⟨x - S.op x, sub_ne_zero.mpr (fun h => hx (h ▸ rfl)), ?_⟩
      have hmap : S.op (x - S.op x) = S.op x - S.op (S.op x) := by simp
      rw [hmap, ← ContinuousLinearMap.comp_apply, S.isIdempotent, sub_self]
  · rintro ⟨⟨a, ha, hae⟩, ⟨b, hb, hbe⟩⟩
    refine ⟨fun h => ha ?_, fun h => hb ?_⟩
    · rw [← hae, h]; simp
    · rw [← hbe, h]; simp
