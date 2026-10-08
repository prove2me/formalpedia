-- Prove2me | solution 1 for AvramDividend.Classical.uniform_integrability_quadratic_tail_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:40:40.807907+00:00
-- url     : https://prove2.me/submissions/9c229734-faee-43d7-94a4-ae7483e8c6ac

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (z R : ℝ) (hz : 0 ≤ z) (hR : 0 < R) :
    (if R < z then z else 0) ≤ z ^ 2 / R := by
  by_cases h : R < z
  · rw [if_pos h]
    apply (le_div_iff₀ hR).2
    nlinarith [mul_nonneg hz (sub_nonneg.mpr (le_of_lt h))]
  · rw [if_neg h]
    exact div_nonneg (sq_nonneg z) (le_of_lt hR)
