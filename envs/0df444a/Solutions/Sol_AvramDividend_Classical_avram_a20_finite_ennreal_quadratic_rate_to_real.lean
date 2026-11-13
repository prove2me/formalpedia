-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_finite_ennreal_quadratic_rate_to_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:35:38.941194+00:00
-- url     : https://prove2.me/submissions/c729ad95-6ee1-4f86-be1a-cae7a6faf6f0

import Mathlib.Data.ENNReal.Inv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal
noncomputable section

theorem solution
    (q : ℝ≥0∞) (hq : q < ⊤) :
    q ^ 2 / 2 = ENNReal.ofReal (q.toReal ^ 2 / 2) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg]
  rw [ENNReal.ofReal_toReal (ne_of_lt hq)]
  norm_num
