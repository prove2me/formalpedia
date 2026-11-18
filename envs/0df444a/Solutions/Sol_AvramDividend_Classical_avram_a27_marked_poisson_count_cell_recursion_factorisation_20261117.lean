-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_marked_poisson_count_cell_recursion_factorisation_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:33:24.938647+00:00
-- url     : https://prove2.me/submissions/8bbd47a3-4294-4b24-8421-cb465c947015

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- A marked-cell Mecke recurrence multiplies Poisson count masses by the mark moment powers. -/
theorem solution (r m : ℝ) (C M : ℕ → ℝ)
    (h0 : C 0 = M 0)
    (hMass : ∀ k : ℕ,
      M (k + 1) = (r / ((k + 1 : ℕ) : ℝ)) * M k)
    (hCell : ∀ k : ℕ,
      C (k + 1) = m * (r / ((k + 1 : ℕ) : ℝ)) * C k) :
    ∀ k : ℕ, C k = M k * m ^ k := by
  intro k
  induction k with
  | zero =>
      simpa using h0
  | succ k hk =>
      rw [hCell k, hMass k, hk, pow_succ]
      ring
