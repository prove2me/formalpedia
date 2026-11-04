-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_actual_count_expectation_le_grid_liminf_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:50:40.721647+00:00
-- url     : https://prove2.me/submissions/0a1ddbbe-c147-4d39-b99f-e73a31c6a266

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal

/-- A pointwise liminf bound on intrinsic counts transfers to an expected
count bound once the measurable finite-grid first moments are controlled. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (g : Ω → ℝ≥0∞) (f : ℕ → Ω → ℝ≥0∞) (C : ℝ≥0∞)
    (hf : ∀ n, Measurable (f n))
    (hpath : ∀ ω, g ω ≤ Filter.liminf (fun n => f n ω) atTop)
    (hmean : Filter.liminf (fun n => ∫⁻ ω, f n ω ∂P) atTop ≤ C) :
    (∫⁻ ω, g ω ∂P) ≤ C := by
  calc
    (∫⁻ ω, g ω ∂P) ≤
        (∫⁻ ω, Filter.liminf (fun n => f n ω) atTop ∂P) :=
      lintegral_mono hpath
    _ ≤ Filter.liminf (fun n => ∫⁻ ω, f n ω ∂P) atTop :=
      lintegral_liminf_le hf
    _ ≤ C := hmean
