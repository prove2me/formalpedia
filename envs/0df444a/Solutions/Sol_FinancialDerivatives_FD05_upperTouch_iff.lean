-- Prove2me | solution 1 for FinancialDerivatives.FD05.upperTouch_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:38:28.830651+00:00
-- url     : https://prove2.me/submissions/86110ee0-ead8-4837-b9b1-4742e7e89b40

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperTouch

open FinancialDerivatives.FD05

theorem solution (B S : ℝ) (monitor : ℕ → Bool) (t : ℕ) :
    upperTouch B S monitor t = true ↔
      monitor t = true ∧ B ≤ S := by
  unfold upperTouch
  simp
