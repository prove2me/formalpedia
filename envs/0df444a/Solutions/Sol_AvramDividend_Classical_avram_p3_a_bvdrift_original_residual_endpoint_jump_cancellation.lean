-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_residual_endpoint_jump_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:24:25.161587+00:00
-- url     : https://prove2.me/submissions/a08baa95-9747-4f7a-bcb5-f52ee3c88501

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_real_jump_total_endpoint_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The actual original BV source's jump at t cancels exactly against
the identical endpoint atom removed from its canonical residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      (((t : ℝ) * X.drift - X.X t ω) - (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal) =
      (((t : ℝ) * X.drift -
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) t) -
          (∑' u : ℝ≥0, if 0 < u ∧ u < t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_real_jump_total_endpoint_split X hBV]
    with ω hω
  intro t ht
  have hsplit := hω t ht
  rw [hsplit]
  ring
