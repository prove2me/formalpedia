-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_poisson_uncentred_second_pmf_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:26:54.080982+00:00
-- url     : https://prove2.me/submissions/f3eb4b0b-6a8c-4218-9c31-21764b3b520c

import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_centered_count_variance_hasSum
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_first_pmf_hasSum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

/-- Exact uncentred second HasSum of the Poisson PMF, by centered moments. -/
theorem solution (r : ℝ≥0) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 2 * (poissonMeasure r).real {n})
      ((r : ℝ) ^ 2 + (r : ℝ)) := by
  have hMass : HasSum (fun n : ℕ => (poissonMeasure r).real {n}) 1 := by
    simpa only [poissonMeasure_real_singleton] using hasSum_one_poissonMeasure r
  have hMean := avram_wave4_p1_poisson_first_pmf_hasSum r
  have hVar := avram_wave4_p1_poisson_centered_count_variance_hasSum r
  have hKey := (hVar.add (hMean.mul_left (2 * (r : ℝ)))).sub
    (hMass.mul_left ((r : ℝ) ^ 2))
  have hFun :
      (fun n : ℕ => (n : ℝ) ^ 2 * (poissonMeasure r).real {n}) =
        fun n : ℕ =>
          (((n : ℝ) - (r : ℝ)) ^ 2 * (poissonMeasure r).real {n} +
            2 * (r : ℝ) * ((n : ℝ) * (poissonMeasure r).real {n})) -
            (r : ℝ) ^ 2 * (poissonMeasure r).real {n} := by
    funext n
    ring
  have hVal : ((r : ℝ) + (2 * (r : ℝ)) * (r : ℝ)) -
      ((r : ℝ) ^ 2) * 1 = ((r : ℝ) ^ 2 + (r : ℝ)) := by
    ring
  rw [hFun, ← hVal]
  exact hKey
