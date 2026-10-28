-- Prove2me | solution 1 for FinancialDerivatives.FD05.initiallyTouched_knockout_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:41:21.46498+00:00
-- url     : https://prove2.me/submissions/095f39a4-a065-471e-8f18-13cdb7a58320

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd03_europeanValue

open FinancialDerivatives.FD03 FinancialDerivatives.FD05


theorem A3FD_out_hit_zero (m : BinomialMarket) (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    ∀ (n t : ℕ) (S : ℝ), europeanValue m n (upperKnockOutTree m B monitor g n t S true) = 0 := by
  intro n
  induction n with
  | zero => intro t S; simp [upperKnockOutTree, europeanValue]
  | succ n ih => intro t S; simp [upperKnockOutTree, europeanValue, ih, oneStepValue]

theorem solution (m : BinomialMarket) (N : ℕ)
    (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ)
    (hM : monitor 0 = true) (hB : B ≤ m.initialSpot) :
    europeanValue m N
      (upperKnockOutTree m B monitor g N 0 m.initialSpot false) = 0 := by
  have h0 : (false || upperTouch B m.initialSpot monitor 0) = true := by simp [upperTouch, hM, hB]
  cases N with
  | zero => simp [upperKnockOutTree, europeanValue, h0]
  | succ n => simp only [upperKnockOutTree, europeanValue, h0, A3FD_out_hit_zero]; simp [oneStepValue]
