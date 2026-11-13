-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_standard_unbounded_cofinal_spatial_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:43:01.236883+00:00
-- url     : https://prove2.me/submissions/e35ad625-1964-437d-ac35-8d37843c0262

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (C : ℝ≥0∞) :
    ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (0 : ℝ) ((k : ℝ) + 1)  := by
  intro y hy _
  obtain ⟨N, hN⟩ := exists_nat_gt y
  refine ⟨N, ?_⟩
  intro k hk
  simp only [mem_Icc]
  constructor
  · exact le_of_lt hy
  · have hReal : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
