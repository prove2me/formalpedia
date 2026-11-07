-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux19_shifted_mesh_exp_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:29:48.916671+00:00
-- url     : https://prove2.me/submissions/eebdee72-4ac7-4298-b500-e652be118266

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
noncomputable section

/-! The n+1 short-cell first-order multiplier converges to the exponential. -/
theorem solution (x : ℝ) :
    Tendsto (fun n : ℕ =>
      (1 - x / ((n : ℝ) + 1)) ^ (n + 1)) atTop
      (𝓝 (Real.exp (-x))) := by
  have h :=
    (Real.tendsto_one_add_div_pow_exp (-x)).comp
      (Filter.tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one,
    neg_div, sub_eq_add_neg] using h
