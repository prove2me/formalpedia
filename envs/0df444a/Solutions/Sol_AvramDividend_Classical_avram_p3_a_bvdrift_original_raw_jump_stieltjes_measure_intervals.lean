-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_stieltjes_measure_intervals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:46:34.829639+00:00
-- url     : https://prove2.me/submissions/332c4db6-2566-486e-b963-4eaf8028a99a

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_stieltjes_function

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- A Stieltjes measure counts the actual accumulated original negative jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ μ : Measure ℝ≥0,
      ∀ a b : ℝ≥0, a ≤ b → μ (Ioc a b) = ENNReal.ofReal (
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_jump_stieltjes_function X hBV]
    with ω hFexists
  obtain ⟨F, hFeq⟩ := hFexists
  refine ⟨F.measure, ?_⟩
  intro a b hab
  simpa only [hFeq a, hFeq b] using (F.measure_Ioc a b)
