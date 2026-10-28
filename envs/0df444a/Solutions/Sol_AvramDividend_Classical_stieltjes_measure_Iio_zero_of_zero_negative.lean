-- Prove2me | solution 1 for AvramDividend.Classical.stieltjes_measure_Iio_zero_of_zero_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:52:21.533328+00:00
-- url     : https://prove2.me/submissions/8c9fecbc-b11c-4536-bf62-af4211f6db32

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Order.Filter.AtTopBot.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

theorem solution
    (S : StieltjesFunction ℝ)
    (hneg : ∀ x : ℝ, x < 0 → S x = 0) :
    S.measure (Iio (0 : ℝ)) = 0 := by
  have hzeroBot : ∀ᶠ y : ℝ in atBot, S y = 0 := by
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with y hy
    exact hneg y hy
  have hbot : Tendsto (S : ℝ → ℝ) atBot (𝓝 (0 : ℝ)) := by
    exact (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (0 : ℝ)) atBot (𝓝 0)).congr'
      (by
        filter_upwards [hzeroBot] with y hy
        exact hy.symm)
  have hzeroLeft : ∀ᶠ y : ℝ in 𝓝[<] (0 : ℝ), S y = 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hneg y hy
  have hleftTend : Tendsto (S : ℝ → ℝ) (𝓝[<] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    exact (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[<] (0 : ℝ)) (𝓝 0)).congr'
      (by
        filter_upwards [hzeroLeft] with y hy
        exact hy.symm)
  have hleft : Function.leftLim (S : ℝ → ℝ) (0 : ℝ) = 0 :=
    leftLim_eq_of_tendsto hleftTend
  rw [S.measure_Iio hbot (0 : ℝ), hleft]
  simp
