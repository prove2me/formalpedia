-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_source_interval_growth_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:59:30.146199+00:00
-- url     : https://prove2.me/submissions/e34fbfda-7efa-435b-916b-ed2341cfdc88

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_interval_cocycle

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- For the original bounded-variation Levy source, the interval growth
plus all actual negative left jumps is bounded by its physical drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      (X.X t ω - X.X s ω) +
        (∑' u : ℝ≥0, if s < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) ≤
      ((t : ℝ) - (s : ℝ)) * X.drift := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_removed_residual_monotone X hBV,
      avram_p3_a_bvdrift_original_raw_removed_residual_interval_cocycle X hBV]
    with ω hmono hcoc
  intro s t hst
  have hnonneg :
      0 ≤
        ((((t : ℝ) * X.drift - X.X t ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) -
        (((s : ℝ) * X.drift - X.X s ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))) :=
    sub_nonneg.mpr (hmono hst)
  rw [hcoc s t hst] at hnonneg
  linarith
