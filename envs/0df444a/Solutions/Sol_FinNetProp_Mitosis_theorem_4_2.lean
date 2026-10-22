-- Prove2me | solution 1 for FinNetProp.Mitosis.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T16:17:12.652663+00:00
-- url     : https://prove2.me/submissions/6c742625-f9ba-44f4-ac3c-e400dbf73a02

import Mathlib
import Definitions.Def_FinNetProp_Mitosis_Setting
import Theorems.Thm_FinNetProp_Mitosis_eisenberg_noe_unique
import Theorems.Thm_FinNetProp_Mitosis_part_I
import Theorems.Thm_FinNetProp_Mitosis_part_II

open FinNetProp.Mitosis in
theorem solution :
    (∀ F : FinNet, ∃! P : ℕ → ℕ → ℝ, IsPropSolution F P) ∧
      ∀ b : BankruptcyRule,
        (ClaimsBounded b ∧ LimitedLiability b ∧ PriorityOfCreditors b ∧ RuleContinuous b ∧
            Impartial b ∧ InvariantToMitosis b) ↔
          ∀ F : FinNet, IsPropSolution F (b F) := by
  refine ⟨eisenberg_noe_unique, fun b => ⟨?_, part_I b⟩⟩
  rintro ⟨hcb, hll, hpc, hcont, himp, hmit⟩
  exact part_II b hcb hll hpc hcont himp hmit
