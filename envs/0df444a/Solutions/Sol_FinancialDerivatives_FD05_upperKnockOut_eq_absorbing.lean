-- Prove2me | solution 1 for FinancialDerivatives.FD05.upperKnockOut_eq_absorbing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:40:55.028073+00:00
-- url     : https://prove2.me/submissions/b1d9a1f4-07f6-42f6-9710-97eb4fe7e606

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_upperAbsorbingValue
import Definitions.Def_fd03_europeanValue

open FinancialDerivatives.FD03 FinancialDerivatives.FD05


theorem A3FD_out_hit_zero (m : BinomialMarket) (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    ∀ (n t : ℕ) (S : ℝ), europeanValue m n (upperKnockOutTree m B monitor g n t S true) = 0 := by
  intro n
  induction n with
  | zero => intro t S; simp [upperKnockOutTree, europeanValue]
  | succ n ih => intro t S; simp [upperKnockOutTree, europeanValue, ih, oneStepValue]

theorem A3FD_absorb (m : BinomialMarket) (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    ∀ (n t : ℕ) (S : ℝ) (hit : Bool),
    upperAbsorbingValue m B monitor g n t S hit =
      europeanValue m n (upperKnockOutTree m B monitor g n t S hit) := by
  intro n
  induction n with
  | zero => intro t S hit; simp [upperAbsorbingValue, upperKnockOutTree, europeanValue]
  | succ n ih =>
    intro t S hit
    by_cases h : (hit || upperTouch B S monitor t) = true
    · simp only [upperAbsorbingValue, upperKnockOutTree, europeanValue, h, if_true,
        A3FD_out_hit_zero]
      simp [oneStepValue]
    · simp only [Bool.not_eq_true] at h
      simp only [upperAbsorbingValue, upperKnockOutTree, europeanValue, h, ih]
      simp

theorem solution (m : BinomialMarket) (N : ℕ)
    (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    upperAbsorbingValue m B monitor g N 0 m.initialSpot false =
      europeanValue m N
        (upperKnockOutTree m B monitor g N 0 m.initialSpot false) := by
  exact A3FD_absorb m B monitor g N 0 m.initialSpot false
