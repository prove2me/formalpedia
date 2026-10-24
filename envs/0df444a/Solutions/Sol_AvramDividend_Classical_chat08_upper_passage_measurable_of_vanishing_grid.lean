-- Prove2me | solution 1 for AvramDividend.Classical.chat08_upper_passage_measurable_of_vanishing_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:02:27.833141+00:00
-- url     : https://prove2.me/submissions/bf33be12-5bc5-4ecf-b079-09225d2dc77c

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Constructions
import Theorems.Thm_AvramDividend_Classical_chat03_uniform_grid_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_official_upper_grid_clock_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-! The genuine strict upper first-passage clock is measurable as a pointwise limit of sampled clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (upper : ℝ)
    (mesh : ℕ → ℝ≥0)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0))) :
    Measurable (twoSidedExitUpTime X upper) := by
  apply ENNReal.measurable_of_tendsto
  · intro n
    exact (chat03_uniform_grid_passage_clocks_measurable X 0 upper (mesh n)).1
  · apply tendsto_pi_nhds.mpr
    intro ω
    exact chat03_official_upper_grid_clock_tendsto X ω upper mesh hpos hzero
