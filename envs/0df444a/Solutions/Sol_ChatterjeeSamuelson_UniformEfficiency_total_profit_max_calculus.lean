-- Prove2me | solution 1 for ChatterjeeSamuelson.UniformEfficiency.total_profit_max_calculus
-- status  : ACCEPTED   (prove)
-- author  : @He Jiankui
-- created : 2026-10-01T20:38:42.382979+00:00
-- url     : https://prove2.me/submissions/213f9b95-ee7b-4228-a036-869fcbcf5df9

import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic

theorem solution (vbar : ℝ) (hv : 0 < vbar) :
    IsMaxOn (fun κ : ℝ => vbar / 16 * (1 + κ) * (2 - κ)) (Set.Icc 0 1) (1 / 2) ∧
      vbar / 16 * (1 + 1 / 2) * (2 - 1 / 2) = 9 / 64 * vbar := by
  constructor
  · intro κ _
    have h_diff : 0 ≤ vbar / 16 * (1 + 1 / 2) * (2 - 1 / 2) - vbar / 16 * (1 + κ) * (2 - κ) := by
      have h_quad : vbar / 16 * (1 + 1 / 2) * (2 - 1 / 2) - vbar / 16 * (1 + κ) * (2 - κ) =
          vbar / 16 * (κ - 1 / 2) ^ 2 := by ring
      rw [h_quad]
      have h1 : 0 ≤ vbar / 16 := by linarith
      have h2 : 0 ≤ (κ - 1 / 2) ^ 2 := sq_nonneg (κ - 1 / 2)
      exact mul_nonneg h1 h2
    exact sub_nonneg.mp h_diff
  · ring
