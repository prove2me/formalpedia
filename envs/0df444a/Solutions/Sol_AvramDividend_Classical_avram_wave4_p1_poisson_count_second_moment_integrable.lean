-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_poisson_count_second_moment_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:26:58.194249+00:00
-- url     : https://prove2.me/submissions/e9522ce9-f77d-4be8-b73f-9d63372aeed6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_centered_count_variance_hasSum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat

/-- A random count with the actual Poisson law has an integrable square and
the correct uncentred second moment, proved from its PMF rather than assumed. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) P) :
    Integrable (fun ω => (K ω : ℝ) ^ 2) P ∧
      (∫ ω, (K ω : ℝ) ^ 2 ∂P) = (r : ℝ) ^ 2 + (r : ℝ) := by
  have hMass : HasSum (fun n : ℕ => (poissonMeasure r).real {n}) 1 := by
    simpa only [poissonMeasure_real_singleton] using hasSum_one_poissonMeasure r
  have hShift1 : ∀ n : ℕ,
      (↑(n + 1) : ℝ) * (poissonMeasure r).real {n + 1} =
        (r : ℝ) * (poissonMeasure r).real {n} := by
    intro n
    simp only [poissonMeasure_real_singleton, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have h1 : (↑(n !) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have h2 : (↑(n + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    field_simp
  have hMean : HasSum
      (fun (n : ℕ) => (n : ℝ) * (poissonMeasure r).real {n}) (r : ℝ) := by
    apply (hasSum_nat_add_iff' 1).mp
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
    simp_rw [hShift1]
    simpa [mul_one] using hMass.mul_left (r : ℝ)
  have hVariance :=
    AvramDividend.Classical.avram_wave4_p1_poisson_centered_count_variance_hasSum r
  have hSecond : HasSum
      (fun n : ℕ => (n : ℝ) ^ 2 * (poissonMeasure r).real {n})
      ((r : ℝ) ^ 2 + (r : ℝ)) := by
    have hKey := (hVariance.add (hMean.mul_left (2 * (r : ℝ)))).sub
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
  let f : ℕ → ℝ := fun n => (n : ℝ) ^ 2
  have hfMeas : Measurable f := by fun_prop
  have hfInt : Integrable f (poissonMeasure r) := by
    rw [integrable_poissonMeasure_iff]
    refine hSecond.summable.congr (fun n => ?_)
    simp only [f, Real.norm_of_nonneg (sq_nonneg _)]
    rw [poissonMeasure_real_singleton]
    try ring
  have hfMean :
      (∫ n, f n ∂poissonMeasure r) = (r : ℝ) ^ 2 + (r : ℝ) := by
    rw [integral_poissonMeasure]
    simp only [smul_eq_mul]
    refine (tsum_congr (fun n => ?_)).trans hSecond.tsum_eq
    rw [poissonMeasure_real_singleton]
    try ring
  constructor
  · have hfMap : Integrable f (Measure.map K P) := by
      rwa [hKlaw.map_eq]
    exact hfMap.comp_measurable hKm
  · simpa [Function.comp_def, f] using
      (hKlaw.integral_comp hfMeas.aestronglyMeasurable).trans hfMean