-- Prove2me | solution 1 for AvramDividend.Classical.exp_gap_dominates_half_interval
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:53:12.229666+00:00
-- url     : https://prove2.me/submissions/e5d25fc0-90ff-493c-a5f9-0bdc57db198d

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution
    (u : ℝ) (hu : 0 ≤ u) (hhalf : u ≤ (1 / 2 : ℝ)) :
    u ≤ 2 * (1 - Real.exp (-u)) := by
  have hE := Real.quadratic_le_exp_of_nonneg hu
  have hpos : 0 < Real.exp u := Real.exp_pos u
  rw [Real.exp_neg]
  have h1 : 1 + u + u ^ 2 / 2 ≤ Real.exp u := hE
  rw [show 2 * (1 - (Real.exp u)⁻¹) = 2 * (Real.exp u - 1) / Real.exp u by field_simp]
  rw [le_div_iff₀ hpos]
  nlinarith [mul_le_mul_of_nonneg_left h1 hu]
