-- Prove2me | solution 1 for AvramDividend.Classical.stieltjes_measure_Iic_of_zero_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:33:41.2964+00:00
-- url     : https://prove2.me/submissions/f348b6af-82eb-49a7-819f-d18855e87f68

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Instances.Real.Lemmas
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

theorem solution
    (S : StieltjesFunction ℝ)
    (hneg : ∀ x : ℝ, x < 0 → S x = 0)
    (x : ℝ) :
    S.measure (Iic x) = ENNReal.ofReal (S x) := by
  have hzero : ∀ᶠ y : ℝ in atBot, S y = 0 := by
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with y hy
    exact hneg y hy
  have htends : Tendsto (S : ℝ → ℝ) atBot (𝓝 (0 : ℝ)) := by
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atBot (𝓝 0)).congr'
      (by
        filter_upwards [hzero] with y hy
        exact hy.symm)
  simpa only [sub_zero] using S.measure_Iic htends x
