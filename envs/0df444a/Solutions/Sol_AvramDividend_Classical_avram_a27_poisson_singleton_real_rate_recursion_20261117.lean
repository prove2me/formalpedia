-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_poisson_singleton_real_rate_recursion_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:41:38.082167+00:00
-- url     : https://prove2.me/submissions/e8241dad-94ca-44a1-ab0c-08ce7e54e9b0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Ordinary real Poisson singleton probabilities obey the rate-over-count recurrence. -/
theorem solution (r : ℝ≥0) (k : ℕ) :
    (poissonMeasure r).real {k + 1} =
      ((r : ℝ) / ((k + 1 : ℕ) : ℝ)) *
        (poissonMeasure r).real {k} := by
  rw [measureReal_def, measureReal_def]
  rw [poissonMeasure_singleton, poissonMeasure_singleton]
  rw [ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)]
  simp only [Nat.factorial_succ, pow_succ, Nat.cast_mul, Nat.cast_succ]
  field_simp
