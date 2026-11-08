-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps10_poisson_exponential_power_memLp_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:31:19.785207+00:00
-- url     : https://prove2.me/submissions/c7ee080e-7066-430f-83e2-9dce97ec9b71

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps10_poisson_power_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite-band Poisson counts have L2 exponential powers, for every
real base, by applying absolute Poisson summability to the squared base. -/
theorem solution (r : ℝ≥0) (a : ℝ) :
    MemLp (fun n : ℕ => a ^ n) 2 (poissonMeasure r) := by
  have hmeas : AEStronglyMeasurable (fun n : ℕ => a ^ n)
      (poissonMeasure r) := (measurable_of_countable _).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hmeas).2
  have hI : Integrable (fun n : ℕ => (a ^ 2) ^ n) (poissonMeasure r) :=
    avram_ubv_ito_jumps10_poisson_power_integrable r (a ^ 2)
  have hEq : (fun n : ℕ => (a ^ n) ^ 2) =
      (fun n : ℕ => (a ^ 2) ^ n) := by
    funext n
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hEq]
  exact hI
