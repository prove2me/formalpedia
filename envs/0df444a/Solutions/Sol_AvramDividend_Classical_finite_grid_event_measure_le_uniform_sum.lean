-- Prove2me | solution 1 for AvramDividend.Classical.finite_grid_event_measure_le_uniform_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:44:13.901852+00:00
-- url     : https://prove2.me/submissions/d1053b8b-feac-4a34-8304-46bcc13d9300

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Uniform bounds on all grid-cell masses control their finite union. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → Set Ω) (N : ℕ) (u : ℝ≥0∞)
    (hCell : ∀ k : ℕ, k < N → μ (A k) ≤ u) :
    μ (⋃ k ∈ Finset.range N, A k) ≤ (N : ℝ≥0∞) * u := by
  calc
    μ (⋃ k ∈ Finset.range N, A k) ≤
        ∑ k ∈ Finset.range N, μ (A k) :=
      measure_biUnion_finset_le (Finset.range N) A
    _ ≤ ∑ k ∈ Finset.range N, u := by
      apply Finset.sum_le_sum
      intro k hk
      exact hCell k (Finset.mem_range.mp hk)
    _ = (N : ℝ≥0∞) * u := by
      simp [nsmul_eq_mul]
