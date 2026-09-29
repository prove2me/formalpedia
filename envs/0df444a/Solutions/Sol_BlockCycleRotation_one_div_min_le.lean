-- Prove2me | solution 1 for BlockCycleRotation.one_div_min_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:31:46.075735+00:00
-- url     : https://prove2.me/submissions/11c281a0-e8ac-47c6-9a71-2971a7205e04

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

end BlockCycleRotation

open BlockCycleRotation in
/-- `1/min(m, a-m) ≤ 1/m + 1/(a-m)`. -/
theorem solution {a m : ℕ} (h0 : 0 < m) (hma : m < a) :
    (1 : ℝ) / ((min m (a - m) : ℕ) : ℝ) ≤ 1 / (m : ℝ) + 1 / ((a - m : ℕ) : ℝ):= by
  have h1 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast h0
  have h2 : (0 : ℝ) < ((a - m : ℕ) : ℝ) := by
    have hpos : 0 < a - m := by omega
    exact_mod_cast hpos
  rcases le_total m (a - m) with h | h
  · rw [min_eq_left h]
    have : (0 : ℝ) < 1 / ((a - m : ℕ) : ℝ) := by positivity
    linarith
  · rw [min_eq_right h]
    have : (0 : ℝ) < 1 / (m : ℝ) := by positivity
    linarith
