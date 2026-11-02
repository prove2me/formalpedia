-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_positive_integer_exponential_primitive_deficit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:15:53.661752+00:00
-- url     : https://prove2.me/submissions/0a678c64-4f8d-4c8f-a1b2-98685a48034a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set

/-! Exact deterministic primitive of an exponential deficit test at any
strictly positive integer mode. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (R : ℝ) :
    (∫ r in (0 : ℝ)..R, Real.exp ((k : ℝ) * (-r))) =
      (1 - Real.exp ((k : ℝ) * (-R))) / (k : ℝ) := by
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  have hbase :
      (-(k : ℝ)) *
        (∫ r in (0 : ℝ)..R, Real.exp ((k : ℝ) * (-r))) =
        Real.exp ((k : ℝ) * (-R)) - 1 := by
    have hh := intervalIntegral.mul_integral_comp_mul_left
      (a := (0 : ℝ)) (b := R) (f := Real.exp) (-(k : ℝ))
    simpa [integral_exp, mul_neg, neg_mul, mul_comm, mul_left_comm, mul_assoc]
      using hh
  apply (eq_div_iff hk0).mpr
  calc
    (∫ r in (0 : ℝ)..R, Real.exp ((k : ℝ) * (-r))) * (k : ℝ) =
        -((-(k : ℝ)) *
          (∫ r in (0 : ℝ)..R, Real.exp ((k : ℝ) * (-r)))) := by ring
    _ = -(Real.exp ((k : ℝ) * (-R)) - 1) := by rw [hbase]
    _ = 1 - Real.exp ((k : ℝ) * (-R)) := by ring
