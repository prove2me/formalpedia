-- Prove2me | solution 1 for FinancialDerivatives.FD05.upperKnockOut_price_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:41:23.776823+00:00
-- url     : https://prove2.me/submissions/90e5d828-fa73-4e37-b8a7-e9c508b25962

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_vanillaTerminalTree
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_payoffTreeLe
import Theorems.Thm_FinancialDerivatives_FD03_european_mono
import Theorems.Thm_FinancialDerivatives_FD03_oneStepValue_mono

open FinancialDerivatives.FD03 FinancialDerivatives.FD05


theorem A3FD_le_vanilla (m : BinomialMarket) (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ)
    (hg : ∀ S : ℝ, 0 ≤ g S) :
    ∀ (n t : ℕ) (S : ℝ) (hit : Bool),
    payoffTreeLe n (upperKnockOutTree m B monitor g n t S hit)
      (payoffTreeMap g n (terminalStockTree m n S)) := by
  intro n
  induction n with
  | zero =>
    intro t S hit
    simp only [upperKnockOutTree, terminalStockTree, payoffTreeMap, payoffTreeLe]
    split_ifs
    · exact hg S
    · exact le_rfl
  | succ n ih =>
    intro t S hit
    simp only [upperKnockOutTree, terminalStockTree, payoffTreeMap, payoffTreeLe]
    exact ⟨ih _ _ _, ih _ _ _⟩

theorem A3FD_nonneg (m : BinomialMarket) (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ)
    (hg : ∀ S : ℝ, 0 ≤ g S) :
    ∀ (n t : ℕ) (S : ℝ) (hit : Bool),
    0 ≤ europeanValue m n (upperKnockOutTree m B monitor g n t S hit) := by
  intro n
  induction n with
  | zero =>
    intro t S hit
    simp only [upperKnockOutTree, europeanValue]
    split_ifs
    · exact le_rfl
    · exact hg S
  | succ n ih =>
    intro t S hit
    simp only [upperKnockOutTree, europeanValue]
    have h0 : oneStepValue m 0 0 = 0 := by simp [oneStepValue]
    rw [← h0]
    exact FinancialDerivatives.FD03.oneStepValue_mono m _ _ _ _ (ih _ _ _) (ih _ _ _)

theorem solution (m : BinomialMarket) (N : ℕ)
    (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ)
    (hg : ∀ S : ℝ, 0 ≤ g S) :
    0 ≤ europeanValue m N
      (upperKnockOutTree m B monitor g N 0 m.initialSpot false) ∧
    europeanValue m N
      (upperKnockOutTree m B monitor g N 0 m.initialSpot false) ≤
    europeanValue m N (vanillaTerminalTree m N g) := by
  refine ⟨A3FD_nonneg m B monitor g hg N 0 m.initialSpot false, ?_⟩
  exact FinancialDerivatives.FD03.european_mono m N _ _ (by simpa only [vanillaTerminalTree] using A3FD_le_vanilla m B monitor g hg N 0 m.initialSpot false)
