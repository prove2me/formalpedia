-- Prove2me | solution 1 for FinancialDerivatives.FD05.upperAbsorbingValue_hit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:38:33.78589+00:00
-- url     : https://prove2.me/submissions/9927660e-d80d-4840-9341-769fae736c8b

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperAbsorbingValue

open FinancialDerivatives.FD03 FinancialDerivatives.FD05

theorem solution (m : BinomialMarket) (B : ℝ)
    (monitor : ℕ → Bool) (g : ℝ → ℝ)
    (n t : ℕ) (S : ℝ) :
    upperAbsorbingValue m B monitor g n t S true = 0 := by
  cases n <;> simp [upperAbsorbingValue]
