-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_poisson_centered_count_variance_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:38:17.48802+00:00
-- url     : https://prove2.me/submissions/52badba4-a797-4f4e-b4b6-69fe2002e930

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat
/-- The centred Poisson count variance follows from the PMF factorial moments. -/
theorem solution
    (r : ℝ≥0) :
    HasSum (fun (n : ℕ) => ((n : ℝ) - (r : ℝ)) ^ 2 *
      (poissonMeasure r).real {n}) (r : ℝ) := by
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
  have hShift2 : ∀ n : ℕ,
      (↑(n + 2) : ℝ) * ↑(n + 1) * (poissonMeasure r).real {n + 2} =
        (r : ℝ) ^ 2 * (poissonMeasure r).real {n} := by
    intro n
    simp only [poissonMeasure_real_singleton, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have h1 : (↑(n !) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have h2 : (↑(n + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have h3 : (↑(n + 2) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  have hFactorial : HasSum
      (fun (n : ℕ) => ((n : ℝ) * ((n : ℝ) - 1)) *
        (poissonMeasure r).real {n}) ((r : ℝ) ^ 2) := by
    apply (hasSum_nat_add_iff' 2).mp
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
      zero_mul, zero_add, sub_self, mul_zero, sub_zero]
    have hShift : ∀ n : ℕ,
        ((↑(n + 2) : ℝ) * (↑(n + 2) - 1)) *
          (poissonMeasure r).real {n + 2} =
          (r : ℝ) ^ 2 * (poissonMeasure r).real {n} := by
      intro n
      have hn : (↑(n + 2) : ℝ) - 1 = ↑(n + 1) := by push_cast; ring
      rw [hn]
      exact hShift2 n
    simp_rw [hShift]
    simpa [mul_one] using hMass.mul_left ((r : ℝ) ^ 2)
  have hSecond : HasSum
      (fun (n : ℕ) => (n : ℝ) ^ 2 * (poissonMeasure r).real {n})
      ((r : ℝ) ^ 2 + r) := by
    convert hFactorial.add hMean using 1
    ext n
    ring
  have hVariance : HasSum
      (fun (n : ℕ) => ((n : ℝ) - (r : ℝ)) ^ 2 *
        (poissonMeasure r).real {n}) (r : ℝ) := by
    have hKey :=
      (hSecond.sub (hMean.mul_left (2 * (r : ℝ)))).add
        (hMass.mul_left ((r : ℝ) ^ 2))
    have hVal : (((r : ℝ) ^ 2 + r) - 2 * (r : ℝ) * (r : ℝ)) +
        (r : ℝ) ^ 2 * 1 = (r : ℝ) := by ring
    rw [hVal] at hKey
    have hFun :
        (fun n : ℕ => ((n : ℝ) - (r : ℝ)) ^ 2 *
          (poissonMeasure r).real {n}) =
        fun n : ℕ => ((n : ℝ) ^ 2 * (poissonMeasure r).real {n} -
          2 * (r : ℝ) * ((n : ℝ) * (poissonMeasure r).real {n})) +
          (r : ℝ) ^ 2 * (poissonMeasure r).real {n} := by
      funext n
      ring
    rw [hFun]
    exact hKey
  exact hVariance
