-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_residual_stieltjes_function
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:05:35.028315+00:00
-- url     : https://prove2.me/submissions/c6f4c754-e060-4582-899d-8e0dd7657f2d

import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_continuous_all_time
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine original BV residual is an increasing right-continuous Stieltjes function. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ F : StieltjesFunction ℝ≥0, ∀ t : ℝ≥0,
      F t = (((t : ℝ) * X.drift - X.X t ω) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_removed_residual_continuous_all_time X hBV,
      avram_p3_a_bvdrift_original_raw_removed_residual_monotone X hBV]
    with ω hcont hmono
  let f : ℝ≥0 → ℝ := fun t =>
    (((t : ℝ) * X.drift - X.X t ω) -
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))
  have hfcont : Continuous f := hcont
  have hfmono : Monotone f := hmono
  refine ⟨StieltjesFunction.mk f hfmono (fun x => hfcont.continuousWithinAt), ?_⟩
  intro t
  rfl
