-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_canonical_residual_interval_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:23:18.549695+00:00
-- url     : https://prove2.me/submissions/693d3ed9-bc95-4646-9839-ef6667b242a0

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_real_negative_jump_additivity
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_real_jump_summable_and_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The residual of the original BV drift minus its true left jumps has
a source-exact interval increment identity after splitting the jump series. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      (((t : ℝ) * X.drift - X.X t ω) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal) -
      (((s : ℝ) * X.drift - X.X s ω) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal) =
      (((t : ℝ) - (s : ℝ)) * X.drift - (X.X t ω - X.X s ω)) -
        (∑' u : ℝ≥0, if s < u ∧ u ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal := by
  filter_upwards
    [avram_p3_a_bvdrift_original_interval_real_negative_jump_additivity X hBV,
     avram_p3_a_bvdrift_original_interval_real_jump_summable_and_tsum X hBV]
    with ω hω haddreal
  intro s t hst
  have hsplit := hω 0 s t (show (0 : ℝ≥0) ≤ s from zero_le) hst
  have hconvt := (haddreal 0 t (show (0 : ℝ≥0) ≤ t from zero_le)).2
  have hconvs := (haddreal 0 s (show (0 : ℝ≥0) ≤ s from zero_le)).2
  have hconvst := (haddreal s t hst).2
  rw [hconvt, hconvs, hconvst]
  rw [hsplit]
  ring
