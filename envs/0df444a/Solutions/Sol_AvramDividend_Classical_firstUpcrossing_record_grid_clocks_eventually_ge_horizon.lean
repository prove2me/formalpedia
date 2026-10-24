-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_record_grid_clocks_eventually_ge_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:57:03.333422+00:00
-- url     : https://prove2.me/submissions/ee430701-c0b5-46be-9a0d-88519871cad4

import Mathlib.Data.Real.Basic
import Theorems.Thm_AvramDividend_Classical_levyPath_no_eventual_record_hit_before_horizon
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_clock_ge_horizon_of_no_hit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-! All sufficiently high uniform-grid first-passage clocks exceed any fixed finite horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (ω : Ω)
    (T : ℝ≥0) (b h : ℝ) (hh : 0 < h) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (T : ℝ≥0∞) ≤
        ⨅ (r : ℝ≥0) (_ : b + (n : ℝ) * h < X.X r ω), (r : ℝ≥0∞) := by
  obtain ⟨N, hN⟩ := levyPath_no_eventual_record_hit_before_horizon X ω T b h hh
  refine ⟨N, ?_⟩
  intro n hn
  exact firstUpcrossing_threshold_clock_ge_horizon_of_no_hit X ω T
    (b + (n : ℝ) * h) (hN n hn)
