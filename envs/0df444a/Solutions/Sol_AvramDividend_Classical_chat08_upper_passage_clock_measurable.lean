-- Prove2me | solution 1 for AvramDividend.Classical.chat08_upper_passage_clock_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:03:36.51527+00:00
-- url     : https://prove2.me/submissions/e4940be2-142a-47b0-b870-e5fe698a6cdb

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Constructions
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_chat03_uniform_grid_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_official_upper_grid_clock_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-! The actual upper exit clock is measurable, including its infinite value, via reciprocals of positive integer meshes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (upper : ℝ) :
    Measurable (twoSidedExitUpTime X upper) := by
  let mesh : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1)
  have hpos : ∀ n, 0 < mesh n := by
    intro n
    dsimp [mesh]
    positivity
  have hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0)) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  apply ENNReal.measurable_of_tendsto
  · intro n
    exact (chat03_uniform_grid_passage_clocks_measurable X 0 upper (mesh n)).1
  · apply tendsto_pi_nhds.mpr
    intro ω
    exact chat03_official_upper_grid_clock_tendsto X ω upper mesh hpos hzero
