-- Prove2me | solution 1 for FinancialDerivatives.FD05.upperAbsorbingValue_alive_maturity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:38:36.518954+00:00
-- url     : https://prove2.me/submissions/7e360cd6-70ad-48cd-81eb-1f10fabdb265

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperAbsorbingValue
import Definitions.Def_fd05_upperTouch

open FinancialDerivatives.FD03 FinancialDerivatives.FD05

theorem solution (m : BinomialMarket)
    (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ)
    (t : ℕ) (S : ℝ) (h : upperTouch B S monitor t = false) :
    upperAbsorbingValue m B monitor g 0 t S false = g S := by
  simp [upperAbsorbingValue, h]
