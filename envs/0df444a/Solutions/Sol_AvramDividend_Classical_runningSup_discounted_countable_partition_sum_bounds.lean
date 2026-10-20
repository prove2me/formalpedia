-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_discounted_countable_partition_sum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:50:14.843822+00:00
-- url     : https://prove2.me/submissions/ebc23ad2-d388-4e7d-8000-fdf4ce2e8d67

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_bounds_record_increment
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (w : ℝ → ℝ≥0∞) (hw : Antitone w)
    (u : ℕ → ℝ) :
    (∑' i : ℕ,
        w (u (i + 1)) *
          ENNReal.ofReal
            (runningSup X (u (i + 1)).toNNReal ω -
             runningSup X (u i).toNNReal ω)) ≤
      (∑' i : ℕ,
        ∫⁻ r, if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0
          ∂(dividendMeasure (runningSup X) ω)) ∧
    (∑' i : ℕ,
        ∫⁻ r, if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0
          ∂(dividendMeasure (runningSup X) ω)) ≤
      (∑' i : ℕ,
        w (u i) *
          ENNReal.ofReal
            (runningSup X (u (i + 1)).toNNReal ω -
             runningSup X (u i).toNNReal ω)) := by
  constructor
  · apply ENNReal.tsum_le_tsum
    intro i
    exact (runningSup_discounted_interval_bounds_record_increment
      X ω w hw (u i) (u (i + 1))).1
  · apply ENNReal.tsum_le_tsum
    intro i
    exact (runningSup_discounted_interval_bounds_record_increment
      X ω w hw (u i) (u (i + 1))).2
