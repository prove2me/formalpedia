-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f2_physical_horizon_rate_real_div
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T01:25:53.182423+00:00
-- url     : https://prove2.me/submissions/7baa97d9-1fc9-4d89-941d-725ef3b0128e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

/-- Convert a physical NNReal time-grid Lévy rate to its real normalisation. -/
theorem solution
    (T : ℝ≥0) (ν : ℝ≥0∞) (k : ℕ) (hk : 0 < k) :
    (((T / (k : ℝ≥0)) : ℝ≥0∞) * ν).toReal =
      (T : ℝ) * ν.toReal / (k : ℝ) := by
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  rw [ENNReal.toReal_mul, ENNReal.toReal_div]
  simp only [ENNReal.coe_toReal, NNReal.coe_natCast]
  ring
