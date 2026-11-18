-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_poisson_source_free_descFactorial_moment_recurrence_20261118
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:37:12.327395+00:00
-- url     : https://prove2.me/submissions/12552d50-79ea-4a73-aef8-d022831f0777

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Real
open scoped NNReal Nat
noncomputable section

theorem solution
    (r : ℝ≥0) (n : ℕ) :
    (∫ k : ℕ, (Nat.descFactorial k (n + 1) : ℝ) ∂poissonMeasure r) =
      (r : ℝ) *
        (∫ k : ℕ, (Nat.descFactorial k n : ℝ) ∂poissonMeasure r) := by
  have hMoment (m : ℕ) :
      (∫ k : ℕ, (Nat.descFactorial k m : ℝ) ∂poissonMeasure r) =
        (r : ℝ) ^ m := by
    have hSeries :
        HasSum
          (fun k : ℕ =>
            Real.exp (-(r : ℝ)) * (r : ℝ) ^ k /
              (k.factorial : ℝ) * (Nat.descFactorial k m : ℝ))
          ((r : ℝ) ^ m) := by
      rw [← hasSum_nat_add_iff' m]
      have hZero :
          ∑ k ∈ Finset.range m,
            Real.exp (-(r : ℝ)) * (r : ℝ) ^ k /
              (k.factorial : ℝ) * (Nat.descFactorial k m : ℝ) = 0 :=
        Finset.sum_eq_zero fun k hk => by
          simp [Nat.descFactorial_eq_zero_iff_lt.2 (Finset.mem_range.1 hk)]
      rw [hZero, sub_zero]
      have hTerm :
          (fun k : ℕ =>
            Real.exp (-(r : ℝ)) * (r : ℝ) ^ (k + m) /
              ((k + m).factorial : ℝ) *
                (Nat.descFactorial (k + m) m : ℝ)) =
          (fun k : ℕ =>
            (r : ℝ) ^ m *
              (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (k.factorial : ℝ))) := by
        funext k
        have h := Nat.factorial_mul_descFactorial (Nat.le_add_left m k)
        rw [Nat.add_sub_cancel] at h
        rw [← h]
        push_cast
        have hNZ : ((k + m).descFactorial m : ℝ) ≠ 0 := by
          exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.not.2 (by omega)
        field_simp
        ring
      rw [hTerm]
      simpa only [mul_one] using
        (hasSum_one_poissonMeasure r).mul_left ((r : ℝ) ^ m)
    rw [integral_poissonMeasure]
    simpa using hSeries.tsum_eq
  rw [hMoment (n + 1), hMoment n, pow_succ]
  ring
