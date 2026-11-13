-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a27_prehorizon_grid_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:41:13.165525+00:00
-- url     : https://prove2.me/submissions/4fa0d68e-1c13-42ad-a5c2-f9faf9da9f40

import Mathlib.Analysis.SpecificLimits.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped NNReal
noncomputable section

theorem solution (n : ℝ≥0) :
    Tendsto (fun m : ℕ => (m : ℝ≥0) * (n / ((m : ℝ≥0) + 1)))
      atTop (nhds n) := by
  have h := tendsto_natCast_div_add_atTop (1 : ℝ≥0)
  have hmul : Tendsto (fun m : ℕ =>
      ((m : ℝ≥0) / ((m : ℝ≥0) + 1)) * n) atTop (nhds n) := by
    simpa using h.mul_const n
  convert hmul using 1
  funext m
  ring
