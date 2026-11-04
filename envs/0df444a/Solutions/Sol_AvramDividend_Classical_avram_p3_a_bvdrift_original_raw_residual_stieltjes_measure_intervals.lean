-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_residual_stieltjes_measure_intervals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:12:04.818895+00:00
-- url     : https://prove2.me/submissions/9ac5e738-f3a0-4417-a306-1f9e1ce7ea5f

import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_residual_stieltjes_function

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine source jump-removed residual induces an exact interval measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ μ : Measure ℝ≥0, ∀ a b : ℝ≥0, a ≤ b →
      μ (Ioc a b) = ENNReal.ofReal (
        ((((b : ℝ) * X.drift - X.X b ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) -
        (((a : ℝ) * X.drift - X.X a ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)))) := by
  filter_upwards [avram_p3_a_bvdrift_original_raw_residual_stieltjes_function X hBV]
    with ω hFexists
  obtain ⟨F, hFeq⟩ := hFexists
  refine ⟨F.measure, ?_⟩
  intro a b hab
  simpa only [hFeq a, hFeq b] using (F.measure_Ioc a b)
