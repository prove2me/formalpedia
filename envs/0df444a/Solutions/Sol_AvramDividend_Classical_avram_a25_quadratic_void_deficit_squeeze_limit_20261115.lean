-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_quadratic_void_deficit_squeeze_limit_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:06:51.887366+00:00
-- url     : https://prove2.me/submissions/efe012d5-ff51-4b75-8e7d-16cf330d4388

import Mathlib.Analysis.SpecificLimits.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
noncomputable section

/-- The first and second count moments squeeze the small-time void slope. -/
theorem solution
    (r : ℝ) (q : ℕ → ℝ)
    (hBounds : ∀ᶠ n in (Filter.atTop : Filter ℕ),
      r - (r ^ 2 / 2) * (1 / ((n : ℕ) : ℝ)) ≤ ((n : ℕ) : ℝ) * q n ∧
        ((n : ℕ) : ℝ) * q n ≤ r) :
    Filter.Tendsto (fun n : ℕ => ((n : ℕ) : ℝ) * q n)
      Filter.atTop (nhds r) := by
  have hInv : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / n)
      Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hMul : Filter.Tendsto
      (fun n : ℕ => (r ^ 2 / 2) * ((1 : ℝ) / n))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hInv)
  have hLower : Filter.Tendsto
      (fun n : ℕ => r - (r ^ 2 / 2) * (1 / ((n : ℕ) : ℝ)))
      Filter.atTop (nhds r) := by
    simpa using (tendsto_const_nhds.sub hMul)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hLower tendsto_const_nhds
  · filter_upwards [hBounds] with n h
    exact h.1
  · filter_upwards [hBounds] with n h
    exact h.2
