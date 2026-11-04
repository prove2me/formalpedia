-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_interval_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:48:45.909393+00:00
-- url     : https://prove2.me/submissions/201d2ade-9309-4cc9-bfa2-750191bb4d7a

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The actual raw-jump-removed source residual has the exact interval cocycle. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      ((((t : ℝ) * X.drift - X.X t ω) - (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) -
        (((s : ℝ) * X.drift - X.X s ω) - (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))) =
      (((t : ℝ) - (s : ℝ)) * X.drift - (X.X t ω - X.X s ω)) -
        (∑' u : ℝ≥0, if s < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity X hBV]
    with ω hadd
  intro s t hst
  rw [hadd s t hst]
  ring
