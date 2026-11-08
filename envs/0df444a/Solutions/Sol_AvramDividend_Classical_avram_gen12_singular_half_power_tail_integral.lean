-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen12_singular_half_power_tail_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:06:53.201211+00:00
-- url     : https://prove2.me/submissions/53a068d9-c5a5-4200-9d8e-de32bbc52bcb

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- The negative-half-power tail provides the regular part of the jump integral. -/
theorem solution
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    (∫ r in y..1, r ^ (-(1 / 2 : ℝ))) =
      2 * (1 - y ^ (1 / 2 : ℝ)) := by
  have hpow : -1 < -(1 / 2 : ℝ) ∨
      -(1 / 2 : ℝ) ≠ -1 ∧ (0 : ℝ) ∉ Set.uIcc y 1 := by
    exact Or.inl (by norm_num)
  rw [integral_rpow hpow]
  norm_num <;> ring
