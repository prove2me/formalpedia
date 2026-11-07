-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_poisson_void_small_time_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:52:21.404959+00:00
-- url     : https://prove2.me/submissions/283fbb1f-412a-4e78-af00-dd0f267602e1

import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-! A second-order bound converts Poisson void probabilities into rare-event errors. -/
theorem solution
    (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    0 ≤ r + Real.exp (-r) - 1 ∧
      r + Real.exp (-r) - 1 ≤ r ^ 2 := by
  have hsmall : |(-r)| ≤ 1 := by
    simpa [abs_neg, abs_of_nonneg h0] using h1
  have hbound := Real.exp_bound (x := -r) (n := 2) hsmall (by norm_num)
  have hquadratic : |Real.exp (-r) - (1 - r)| ≤ r ^ 2 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero,
      abs_neg, abs_of_nonneg h0] at hbound
    have hratio : r ^ 2 * (3 / 4 : ℝ) ≤ r ^ 2 := by
      nlinarith [sq_nonneg r]
    exact le_trans (by simpa [sub_eq_add_neg] using hbound) hratio
  constructor
  · nlinarith [Real.add_one_le_exp (-r)]
  · rcases abs_le.mp hquadratic with ⟨_, hupper⟩
    nlinarith
