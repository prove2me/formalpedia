-- Prove2me | solution 1 for FinancialDerivatives.FD05.upperTouch_antitone_barrier
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:38:31.338541+00:00
-- url     : https://prove2.me/submissions/0acef122-6928-496e-ab44-c5e3bf21bd15

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperTouch

open FinancialDerivatives.FD05

theorem solution (B₁ B₂ S : ℝ)
    (monitor : ℕ → Bool) (t : ℕ) (hB : B₁ ≤ B₂)
    (h : upperTouch B₂ S monitor t = true) :
    upperTouch B₁ S monitor t = true := by
  unfold upperTouch at *
  simp only [Bool.and_eq_true, decide_eq_true_eq] at *
  exact ⟨h.1, hB.trans h.2⟩
