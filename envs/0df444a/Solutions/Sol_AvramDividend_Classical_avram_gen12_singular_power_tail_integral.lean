-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen12_singular_power_tail_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:02:58.319788+00:00
-- url     : https://prove2.me/submissions/307d676d-34b0-4c2c-979a-fa307bba0423

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- The finite negative-three-halves-power tail grows as the inverse square root. -/
theorem solution
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    (∫ r in y..1, r ^ (-(3 / 2 : ℝ))) =
      2 * (y ^ (-(1 / 2 : ℝ)) - 1) := by
  have hzero : (0 : ℝ) ∉ Set.uIcc y 1 := by
    rw [Set.uIcc_of_le hy1]
    exact fun hz => (not_le.mpr hy) hz.1
  have hpow : -1 < -(3 / 2 : ℝ) ∨
      -(3 / 2 : ℝ) ≠ -1 ∧ (0 : ℝ) ∉ Set.uIcc y 1 := by
    exact Or.inr ⟨by norm_num, hzero⟩
  rw [integral_rpow hpow]
  norm_num
  ring
