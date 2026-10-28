-- Prove2me | solution 1 for FinancialDerivatives.FD03.oneStepValue_mono
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:58:28.687557+00:00
-- url     : https://prove2.me/submissions/835cd768-1d44-4f29-a879-95cf8ee54ab1

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Definitions.Def_fd03_oneStepValue
open FinancialDerivatives.FD03
theorem solution (m : BinomialMarket)
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
