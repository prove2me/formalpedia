-- Prove2me | solution 1 for FinancialDerivatives.FD03.optimal_policy_exists
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:03:15.104138+00:00
-- url     : https://prove2.me/submissions/46ee9cf2-10f5-46af-aa5f-b7deb26d152d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Definitions.Def_fd03_admissible
import Definitions.Def_fd03_policyValue
import Definitions.Def_fd03_snellValue
open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket) (n : ℕ)
    (tree : ExerciseTree n) :
    ∃ p : StoppingPolicy n,
      admissible tree p ∧ policyValue m n tree p = snellValue m n tree := by

  induction tree with
  | maturity r => exact ⟨.maturity, trivial, rfl⟩
  | node allowed reward up down ihu ihd =>
    obtain ⟨pU, hU, eU⟩ := ihu
    obtain ⟨pD, hD, eD⟩ := ihd
    have hc : policyValue m _ (.node allowed reward up down) (.continue pU pD) =
        oneStepValue m (snellValue m _ up) (snellValue m _ down) := by
      show oneStepValue m (policyValue m _ up pU) (policyValue m _ down pD) = _
      rw [eU, eD]
    cases allowed
    · exact ⟨.continue pU pD, ⟨hU, hD⟩, hc⟩
    · by_cases h : oneStepValue m (snellValue m _ up) (snellValue m _ down) ≤ reward
      · refine ⟨.stop, rfl, ?_⟩
        show reward = max reward _
        exact (max_eq_left h).symm
      · refine ⟨.continue pU pD, ⟨hU, hD⟩, ?_⟩
        rw [hc]
        show _ = max reward _
        exact (max_eq_right (le_of_not_ge h)).symm
