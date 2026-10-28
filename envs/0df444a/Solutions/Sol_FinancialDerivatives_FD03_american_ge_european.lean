-- Prove2me | solution 1 for FinancialDerivatives.FD03.american_ge_european
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:07:45.943808+00:00
-- url     : https://prove2.me/submissions/a466308a-a15b-4d5e-ba1c-70085320bdd0

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_terminalStockTree
import Definitions.Def_fd03_payoffTreeMap
import Definitions.Def_fd03_snellValue
import Definitions.Def_fd03_exerciseStockTree
import Mathlib.Tactic
import Definitions.Def_fd03_oneStepValue
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

theorem solution (m : BinomialMarket)
    (n : ℕ) (spot : ℝ) (reward : ℝ → ℝ) :
    europeanValue m n
      (payoffTreeMap reward n (terminalStockTree m n spot)) ≤
      snellValue m n
        (exerciseStockTree m reward (fun _ => true) n spot) := by


  induction n generalizing spot with
  | zero => exact le_rfl
  | succ n ih =>
    show oneStepValue m _ _ ≤ max (reward spot) (oneStepValue m _ _)
    exact (S200F_mono m _ _ _ _ (ih (spot * m.up)) (ih (spot * m.down))).trans (le_max_right _ _)
