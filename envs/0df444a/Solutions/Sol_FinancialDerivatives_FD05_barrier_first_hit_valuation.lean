-- Prove2me | solution 1 for FinancialDerivatives.FD05.barrier_first_hit_valuation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:44:16.540302+00:00
-- url     : https://prove2.me/submissions/723f67c8-03d0-4f54-93ef-1eaf7d538145

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_upperKnockInTree
import Definitions.Def_fd05_upperAbsorbingValue
import Definitions.Def_fd05_discountedSurvivalPathPrice
import Definitions.Def_fd05_vanillaTerminalTree
import Definitions.Def_fd03_europeanValue
import Theorems.Thm_FinancialDerivatives_FD05_upperKnockOut_eq_absorbing
import Theorems.Thm_FinancialDerivatives_FD05_upperKnockInOut_price_parity
import Theorems.Thm_FinancialDerivatives_FD05_upperKnockOut_eq_path_sum

open FinancialDerivatives.FD03 FinancialDerivatives.FD05

theorem solution (m : BinomialMarket) (N : ℕ)
    (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    (upperAbsorbingValue m B monitor g N 0 m.initialSpot false =
      europeanValue m N
        (upperKnockOutTree m B monitor g N 0 m.initialSpot false)) ∧
    (europeanValue m N
      (upperKnockOutTree m B monitor g N 0 m.initialSpot false) =
      discountedSurvivalPathPrice m N B monitor g) ∧
    (europeanValue m N
      (upperKnockInTree m B monitor g N 0 m.initialSpot false) +
      europeanValue m N
        (upperKnockOutTree m B monitor g N 0 m.initialSpot false) =
      europeanValue m N (vanillaTerminalTree m N g)) := by
  exact ⟨FinancialDerivatives.FD05.upperKnockOut_eq_absorbing m N B monitor g,
    FinancialDerivatives.FD05.upperKnockOut_eq_path_sum m N B monitor g,
    FinancialDerivatives.FD05.upperKnockInOut_price_parity m N B monitor g⟩
