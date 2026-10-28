-- Prove2me | solution 1 for FinancialDerivatives.FD03.bermudan_schedule_mono
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:07:50.324295+00:00
-- url     : https://prove2.me/submissions/211e717a-ea54-473f-bcca-03c64ae2bbc4

import Mathlib.Data.Real.Basic
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
    (n : ℕ) (spot : ℝ) (reward : ℝ → ℝ)
    (A B : ℕ → Bool) (hAB : ∀ k, A k = true → B k = true) :
    snellValue m n (exerciseStockTree m reward A n spot) ≤
      snellValue m n (exerciseStockTree m reward B n spot) := by


  induction n generalizing spot with
  | zero => exact le_rfl
  | succ n ih =>
    have hc := S200F_mono m _ _ _ _ (ih (spot * m.up)) (ih (spot * m.down))
    show (match A (n + 1) with
        | true => max (reward spot) (oneStepValue m _ _)
        | false => oneStepValue m _ _) ≤
      (match B (n + 1) with
        | true => max (reward spot) (oneStepValue m _ _)
        | false => oneStepValue m _ _)
    cases hA : A (n + 1) <;> cases hB : B (n + 1)
    · exact hc
    · exact hc.trans (le_max_right _ _)
    · exact absurd (hAB _ hA) (by simp [hB])
    · exact max_le_max le_rfl hc
