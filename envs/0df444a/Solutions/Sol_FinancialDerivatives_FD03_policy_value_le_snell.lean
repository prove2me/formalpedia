-- Prove2me | solution 1 for FinancialDerivatives.FD03.policy_value_le_snell
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:03:10.956426+00:00
-- url     : https://prove2.me/submissions/a8b66ef0-f292-473b-abf0-9227e383c0f6

import Mathlib.Tactic
import Definitions.Def_fd03_oneStepValue
import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_admissible
import Definitions.Def_fd03_policyValue
import Definitions.Def_fd03_snellValue

open FinancialDerivatives.FD03

theorem S200F_mono (m : BinomialMarket)
    (u₁ u₂ d₁ d₂ : ℝ) (hu : u₁ ≤ u₂) (hd : d₁ ≤ d₂) :
    oneStepValue m u₁ d₁ ≤ oneStepValue m u₂ d₂ := by
  unfold oneStepValue
  have h1 := m.down_lt_growth
  have h2 := m.growth_lt_up
  have h3 := m.down_pos
  have hp : 0 < upWeight m := by unfold upWeight; apply div_pos <;> linarith
  have hq : upWeight m < 1 := by unfold upWeight; rw [div_lt_one (by linarith)]; linarith
  apply div_le_div_of_nonneg_right _ (by linarith)
  nlinarith

open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket) (n : ℕ)
    (tree : ExerciseTree n) (p : StoppingPolicy n)
    (hp : admissible tree p) :
    policyValue m n tree p ≤ snellValue m n tree := by

  induction tree with
  | maturity r =>
    cases p
    rfl
  | node allowed reward up down ihu ihd =>
    cases p with
    | stop =>
      simp only [admissible] at hp
      subst hp
      show reward ≤ max reward _
      exact le_max_left _ _
    | «continue» pU pD =>
      simp only [admissible] at hp
      have h := S200F_mono m _ _ _ _ (ihu pU hp.1) (ihd pD hp.2)
      cases allowed
      · exact h
      · exact h.trans (le_max_right _ _)
