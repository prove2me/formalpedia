-- Prove2me | solution 1 for BalanceSpecification.FiniteEntropy.mul_log_div
-- status  : ACCEPTED   (prove)
-- author  : @Mceppaglia
-- created : 2026-11-24T02:04:04.487506+00:00
-- url     : https://prove2.me/submissions/4514d308-09ed-4d7f-aa18-bedee408ded6

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public section

theorem solution {p q : ℝ} (hq : 0 < q) :
    p * Real.log (p / q) = p * Real.log p - p * Real.log q := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [Real.log_div hp hq.ne', mul_sub]
