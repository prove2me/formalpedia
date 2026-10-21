-- Prove2me | solution 1 for AvramDividend.Classical.chat03_finite_grid_clock_tendsto_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T21:59:55.847863+00:00
-- url     : https://prove2.me/submissions/d569db1d-f74b-4d80-835f-94e6af71f196

import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal ENNReal

/-!
Passing a convergent finite NNReal first-passage clock to ENNReal
preserves its finite limit, including the zero boundary case.
-/
theorem solution
    (τ : ℝ≥0∞) (hτ : τ ≠ ∞) (σ : ℕ → ℝ≥0)
    (hσ : Tendsto σ atTop (𝓝 τ.toNNReal)) :
    Tendsto (fun n => (σ n : ℝ≥0∞)) atTop (𝓝 τ) := by
  have hc :
      Tendsto (fun n => (σ n : ℝ≥0∞)) atTop
        (𝓝 (τ.toNNReal : ℝ≥0∞)) :=
    ENNReal.continuous_coe.tendsto τ.toNNReal |>.comp hσ
  simpa only [ENNReal.coe_toNNReal hτ] using hc
