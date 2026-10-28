-- Prove2me | solution 1 for AvramDividend.Classical.stieltjes_measure_univ_le_one_of_zero_negative_bounded_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:03:21.049322+00:00
-- url     : https://prove2.me/submissions/743d5db1-50fb-470d-8a2d-99919dbeeefc

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Filter.AtTopBot.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem solution
    (S : StieltjesFunction ℝ)
    (hneg : ∀ x : ℝ, x < 0 → S x = 0)
    (hbound : ∀ x : ℝ, S x ≤ 1) :
    S.measure Set.univ ≤ 1 := by
  have hzero : ∀ᶠ x : ℝ in atBot, S x = 0 := by
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    exact hneg x hx
  have hbot : Tendsto (S : ℝ → ℝ) atBot (𝓝 (0 : ℝ)) := by
    exact (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (0 : ℝ)) atBot (𝓝 0)).congr'
      (by
        filter_upwards [hzero] with x hx
        exact hx.symm)
  have hbdd : BddAbove (Set.range (S : ℝ → ℝ)) := by
    refine ⟨1, ?_⟩
    rintro z ⟨x, rfl⟩
    exact hbound x
  have htop : Tendsto (S : ℝ → ℝ) atTop
      (𝓝 (⨆ x : ℝ, S x)) :=
    tendsto_atTop_ciSup S.mono hbdd
  have htopBound : (⨆ x : ℝ, S x) ≤ 1 :=
    ciSup_le fun x => hbound x
  rw [S.measure_univ hbot htop]
  simpa only [sub_zero, ENNReal.ofReal_one] using
    ENNReal.ofReal_le_ofReal htopBound
