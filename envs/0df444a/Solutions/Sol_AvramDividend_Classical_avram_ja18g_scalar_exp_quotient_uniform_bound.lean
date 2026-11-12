-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_scalar_exp_quotient_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:32:49.001803+00:00
-- url     : https://prove2.me/submissions/adcd7082-d078-4632-b09a-15aa1f5ed279

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Uniform scalar domination from convexity of the real exponential. -/
theorem solution
    (x θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    |(Real.exp (θ * x) - 1) / θ| ≤
      |x| + 1 + Real.exp (2 * x) := by
  have hconv : Real.exp (θ * x) ≤
      1 - θ + θ * Real.exp x := by
    have h := convexOn_exp.2
      (Set.mem_univ (0 : ℝ)) (Set.mem_univ x)
      (sub_nonneg.mpr hθ1) (le_of_lt hθ)
      (by ring : (1 - θ) + θ = (1 : ℝ))
    simpa [smul_eq_mul, Real.exp_zero] using h
  have hLower : x ≤ (Real.exp (θ * x) - 1) / θ := by
    rw [le_div_iff₀ hθ]
    nlinarith [Real.add_one_le_exp (θ * x)]
  have hUpper : (Real.exp (θ * x) - 1) / θ ≤
      Real.exp x - 1 := by
    rw [div_le_iff₀ hθ]
    linarith
  have hExpBound : Real.exp x ≤ 1 + Real.exp (2 * x) := by
    by_cases hx : 0 ≤ x
    · have hxx : x ≤ 2 * x := by linarith
      have h := Real.exp_le_exp.mpr hxx
      linarith
    · have hxx : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
      have h := Real.exp_le_exp.mpr hxx
      have hp := Real.exp_pos (2 * x)
      have hExpLe : Real.exp x ≤ 1 := by
        simpa only [Real.exp_zero] using h
      linarith
  apply abs_le.mpr
  constructor
  · have hneg := neg_abs_le x
    have hp := Real.exp_pos (2 * x)
    linarith
  · have hp := abs_nonneg x
    linarith
