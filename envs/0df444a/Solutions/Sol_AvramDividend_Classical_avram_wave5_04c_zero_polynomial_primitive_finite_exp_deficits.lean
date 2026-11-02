-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_zero_polynomial_primitive_finite_exp_deficits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:19:15.954467+00:00
-- url     : https://prove2.me/submissions/4cb24513-5ec3-410b-aff8-5a55503f2fe9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_zero_constant_polynomial_exact_finite_exp_modes
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_positive_integer_exponential_primitive_deficit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set
open AvramDividend.Classical
open scoped BigOperators

/-! The primitive of every zero-constant exponential-coordinate polynomial
is a finite signed sum of genuine positive-integer exponential deficits. -/
theorem solution (p : Polynomial ℝ) (hp : Polynomial.eval 0 p = 0)
    (R : ℝ) :
    (∫ r in (0 : ℝ)..R, Polynomial.eval (Real.exp (-r)) p) =
      ∑ k ∈ p.support.erase 0,
        p.coeff k *
          ((1 - Real.exp ((k : ℝ) * (-R))) / (k : ℝ)) := by
  calc
    (∫ r in (0 : ℝ)..R, Polynomial.eval (Real.exp (-r)) p) =
        (∫ r in (0 : ℝ)..R,
          ∑ k ∈ p.support.erase 0,
            p.coeff k * Real.exp ((k : ℝ) * (-r))) := by
              apply intervalIntegral.integral_congr
              intro r hr
              exact avram_wave5_04c_zero_constant_polynomial_exact_finite_exp_modes p hp r
    _ = ∑ k ∈ p.support.erase 0,
          (∫ r in (0 : ℝ)..R,
            p.coeff k * Real.exp ((k : ℝ) * (-r))) := by
              apply intervalIntegral.integral_finset_sum
              intro k hk
              have hc : Continuous
                  (fun r : ℝ => p.coeff k * Real.exp ((k : ℝ) * (-r))) := by
                fun_prop
              exact hc.intervalIntegrable _ _
    _ = ∑ k ∈ p.support.erase 0,
          p.coeff k *
            (∫ r in (0 : ℝ)..R, Real.exp ((k : ℝ) * (-r))) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [intervalIntegral.integral_const_mul]
    _ = ∑ k ∈ p.support.erase 0,
          p.coeff k *
            ((1 - Real.exp ((k : ℝ) * (-R))) / (k : ℝ)) := by
              apply Finset.sum_congr rfl
              intro k hk
              have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
              have hk1 : 1 ≤ k := by omega
              rw [avram_wave5_04c_positive_integer_exponential_primitive_deficit k hk1 R]
