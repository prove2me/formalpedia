-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_poisson_first_pmf_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:21:33.098965+00:00
-- url     : https://prove2.me/submissions/343692c1-a0bd-4f1e-85fe-fbfe3b98037c

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat

/-- The exact first moment of the Poisson PMF, with absolute summability. -/
theorem solution (r : ℝ≥0) :
    HasSum (fun n : ℕ =>
      (n : ℝ) * (poissonMeasure r).real {n}) (r : ℝ) := by
  have hMass : HasSum (fun n : ℕ => (poissonMeasure r).real {n}) 1 := by
    simpa only [poissonMeasure_real_singleton] using hasSum_one_poissonMeasure r
  have hShift : ∀ n : ℕ,
      (↑(n + 1) : ℝ) * (poissonMeasure r).real {n + 1} =
        (r : ℝ) * (poissonMeasure r).real {n} := by
    intro n
    simp only [poissonMeasure_real_singleton, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have h1 : (↑(n !) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have h2 : (↑(n + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    field_simp
  apply (hasSum_nat_add_iff' 1).mp
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
  simp_rw [hShift]
  simpa [mul_one] using hMass.mul_left (r : ℝ)
