-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_atom_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:05:31.468467+00:00
-- url     : https://prove2.me/submissions/08f86eca-6aec-439b-a8ed-9cf480908e6b

import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal

/-- The positive-time Gaussian double-tail jump atom decreases with time. -/
theorem solution (φ s t z : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    (if 0 < t ∧ t < z then
      ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-φ * z))
     else 0) ≤
    (if 0 < s ∧ s < z then
      ENNReal.ofReal (z - s) * ENNReal.ofReal (Real.exp (-φ * z))
     else 0) := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  by_cases htz : t < z
  · have hsz : s < z := lt_of_le_of_lt hst htz
    rw [if_pos ⟨ht, htz⟩, if_pos ⟨hs, hsz⟩]
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (by linarith)) bot_le
  · have hbad : ¬ (0 < t ∧ t < z) := fun h => htz h.2
    simp [hbad]
