-- Prove2me | solution 1 for BookProof.ChapterEulerStochastic.preservesProb_iff_exists_angles
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:54:31.038208+00:00
-- url     : https://prove2.me/submissions/e1b268c5-ab30-410f-827f-ea52f5a507aa

-- Generated from ChapterEulerStochastic.lean — solution of BookProof.ChapterEulerStochastic.preservesProb_iff_exists_angles
import Mathlib
import Definitions.Def_ChapterEulerStochastic
import Theorems.Thm_BookProof_ChapterEulerStochastic_exists_cos_sq
import Theorems.Thm_BookProof_ChapterEulerStochastic_Mmat_preservesProb
import Theorems.Thm_BookProof_ChapterEulerStochastic_preservesProb_iff_columnStochastic
open BookProof.ChapterEulerStochastic



open scoped Matrix BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (M : Matrix (Fin 2) (Fin 2) ℝ) :
    PreservesProb M ↔ ∃ a b : ℝ, M = Mmat a b := by

      constructor <;> intro h
      · -- Both columns are probability vectors
        obtain ⟨h00, h01, h10, h11, hsum⟩ : 0 ≤ M 0 0 ∧ 0 ≤ M 0 1 ∧ 0 ≤ M 1 0 ∧
            0 ≤ M 1 1 ∧ M 0 0 + M 1 0 = 1 ∧ M 0 1 + M 1 1 = 1 := by
          have := preservesProb_iff_columnStochastic M |>.1 h
          simp_all [Fin.forall_fin_two, IsProbVec]
        obtain ⟨a, ha⟩ : ∃ a : ℝ, Real.cos a ^ 2 = M 0 0 := exists_cos_sq h00 (by linarith)
        obtain ⟨b, hb⟩ : ∃ b : ℝ, Real.cos b ^ 2 = M 0 1 := exists_cos_sq h01 (by linarith)
        use a, b; ext i j; fin_cases i <;> fin_cases j
          <;> simp [*, Mmat] <;>
          linarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b]
      · exact h.elim fun a ha => ha.elim fun b hb => hb ▸ Mmat_preservesProb a b
