-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_poisson_weighted_count_transform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:54:29.203412+00:00
-- url     : https://prove2.me/submissions/6205c7d2-3af6-4f2c-a279-388d957c46d9

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
noncomputable section

theorem solution
    (rate q : ℝ) :
    (∑' m : ℕ, Real.exp (-rate) *
      (rate ^ m / (m.factorial : ℝ)) * Real.exp (-(m : ℝ) * q)) =
    Real.exp (rate * (Real.exp (-q) - 1)) := by
  have hexp (m : ℕ) :
      Real.exp (-(m : ℝ) * q) = Real.exp (-q) ^ m := by
    calc
      Real.exp (-(m : ℝ) * q) =
          Real.exp ((m : ℝ) * (-q)) := by congr 1; ring
      _ = Real.exp (-q) ^ m := Real.exp_nat_mul (-q) m
  calc
    (∑' m : ℕ, Real.exp (-rate) *
        (rate ^ m / (m.factorial : ℝ)) * Real.exp (-(m : ℝ) * q)) =
      (∑' m : ℕ, Real.exp (-rate) *
        ((rate * Real.exp (-q)) ^ m / (m.factorial : ℝ))) := by
          apply tsum_congr
          intro m
          rw [hexp m, mul_pow]
          ring
    _ = Real.exp (-rate) *
      (∑' m : ℕ, (rate * Real.exp (-q)) ^ m / (m.factorial : ℝ)) := by
        exact tsum_mul_left
    _ = Real.exp (-rate) * Real.exp (rate * Real.exp (-q)) := by
        congr 1
        have hseries : Real.exp (rate * Real.exp (-q)) =
            (∑' m : ℕ, (rate * Real.exp (-q)) ^ m / (m.factorial : ℝ)) := by
              rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
        exact hseries.symm
    _ = Real.exp (rate * (Real.exp (-q) - 1)) := by
        rw [← Real.exp_add]
        congr 1
        ring
