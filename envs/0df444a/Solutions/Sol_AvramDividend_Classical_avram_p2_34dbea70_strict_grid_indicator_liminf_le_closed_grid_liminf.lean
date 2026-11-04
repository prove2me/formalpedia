-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_strict_grid_indicator_liminf_le_closed_grid_liminf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:46:53.12093+00:00
-- url     : https://prove2.me/submissions/b63474d5-b31e-4d09-9c03-57645c4c2fd9

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

/-- A strict negative threshold grid count is pointwise bounded by its
closed-threshold indicator count, uniformly in the grid resolution. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (u : ℕ → ℕ → Ω → ℝ) (a : ℝ) (C : ℝ≥0∞)
    (hmean : Filter.liminf (fun n : ℕ =>
      ∫⁻ ω, ∑ i ∈ Finset.range (n + 1),
        (Iic a).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) (u n i ω) ∂P)
          atTop ≤ C) :
    Filter.liminf (fun n : ℕ =>
      ∫⁻ ω, ∑ i ∈ Finset.range (n + 1),
        (if u n i ω < a then (1 : ℝ≥0∞) else 0) ∂P)
        atTop ≤ C := by
  have hpoint (z : ℝ) :
      (if z < a then (1 : ℝ≥0∞) else 0) ≤
        (Iic a).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) z := by
    by_cases hlt : z < a
    · have hle : z ≤ a := le_of_lt hlt
      simp [hlt, hle]
    · by_cases hle : z ≤ a
      · simp [hlt, hle]
      · simp [hlt, hle]
  have hevent : ∀ᶠ n : ℕ in atTop,
      (∫⁻ ω, ∑ i ∈ Finset.range (n + 1),
        (if u n i ω < a then (1 : ℝ≥0∞) else 0) ∂P) ≤
      (∫⁻ ω, ∑ i ∈ Finset.range (n + 1),
        (Iic a).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) (u n i ω) ∂P) := by
    filter_upwards [] with n
    apply lintegral_mono
    intro ω
    exact Finset.sum_le_sum (fun i hi => hpoint (u n i ω))
  exact (Filter.liminf_le_liminf hevent).trans hmean
