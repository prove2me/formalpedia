-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_discounted_partition_sum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:31:45.136989+00:00
-- url     : https://prove2.me/submissions/f1e36b68-7f25-40f0-853b-aaf4508be26d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_bounds_record_increment
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/- Finite-sum bounds for genuine discounted record-increment Stieltjes rewards. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (w : ℝ → ℝ≥0∞) (hw : Antitone w)
    (u : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n,
        w (u (i + 1)) *
          ENNReal.ofReal
            (runningSup X (u (i + 1)).toNNReal ω -
             runningSup X (u i).toNNReal ω)) ≤
      (∑ i ∈ Finset.range n,
        ∫⁻ r, if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0
          ∂(dividendMeasure (runningSup X) ω)) ∧
    (∑ i ∈ Finset.range n,
        ∫⁻ r, if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0
          ∂(dividendMeasure (runningSup X) ω)) ≤
      (∑ i ∈ Finset.range n,
        w (u i) *
          ENNReal.ofReal
            (runningSup X (u (i + 1)).toNNReal ω -
             runningSup X (u i).toNNReal ω)) := by
  constructor
  · apply Finset.sum_le_sum
    intro i hi
    exact (runningSup_discounted_interval_bounds_record_increment
      X ω w hw (u i) (u (i + 1))).1
  · apply Finset.sum_le_sum
    intro i hi
    exact (runningSup_discounted_interval_bounds_record_increment
      X ω w hw (u i) (u (i + 1))).2
