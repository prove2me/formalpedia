-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a84_centered_gaussian_quadratic_cross_young_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:06:16.605967+00:00
-- url     : https://prove2.me/submissions/6c161255-118e-4899-a7cb-e15e1cc5b950

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- Elementary Young bound for the actual Gaussian centred increment and physical deterministic drift. -/
theorem solution (z d ε : ℝ) (hε : 0 < ε) :
    2 * |d| * |z| ≤ ε * z^2 + d^2 / ε := by
  have hh : 2 * ε * |d| * |z| ≤ ε^2 * z^2 + d^2 := by
    nlinarith [sq_nonneg (ε * |z| - |d|), sq_abs z, sq_abs d]
  have hp : (2 * |d| * |z|) * ε ≤ ε^2 * z^2 + d^2 := by
    nlinarith [hh]
  have hdiv : 2 * |d| * |z| ≤ (ε^2 * z^2 + d^2) / ε :=
    (le_div_iff₀ hε).mpr hp
  calc
    2 * |d| * |z| ≤ (ε^2 * z^2 + d^2) / ε := hdiv
    _ = ε * z^2 + d^2 / ε := by
      field_simp [ne_of_gt hε] <;> ring
