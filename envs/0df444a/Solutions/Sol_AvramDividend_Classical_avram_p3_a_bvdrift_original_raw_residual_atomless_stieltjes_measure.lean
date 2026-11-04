-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_residual_atomless_stieltjes_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:24:41.117417+00:00
-- url     : https://prove2.me/submissions/1862d3a7-ca4c-4b62-a2d2-6c20289f1ce5

import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_residual_stieltjes_function
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_continuous_all_time

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The continuous original BV drift-removal residual induces no atomic mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ μ : Measure ℝ≥0,
      (∀ a b : ℝ≥0, a ≤ b →
        μ (Ioc a b) = ENNReal.ofReal (
          ((((b : ℝ) * X.drift - X.X b ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) -
          (((a : ℝ) * X.drift - X.X a ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))))) ∧
      (∀ a : ℝ≥0, μ {a} = 0) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_residual_stieltjes_function X hBV,
      avram_p3_a_bvdrift_original_raw_removed_residual_continuous_all_time X hBV]
    with ω hFexists hcont
  obtain ⟨F, hFeq⟩ := hFexists
  have hF_eq : (F : ℝ≥0 → ℝ) = (fun t : ℝ≥0 =>
      (((t : ℝ) * X.drift - X.X t ω) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))) :=
    funext hFeq
  have hFcont : Continuous (F : ℝ≥0 → ℝ) := by
    rw [hF_eq]
    exact hcont
  refine ⟨F.measure, ?_, ?_⟩
  · intro a b hab
    simpa only [hFeq a, hFeq b] using (F.measure_Ioc a b)
  · intro a
    rw [F.measure_singleton]
    have hAt : ContinuousAt (F : ℝ≥0 → ℝ) a := hFcont.continuousAt
    have hleft : Function.leftLim (F : ℝ≥0 → ℝ) a = F a :=
      hAt.continuousWithinAt.leftLim_eq
    simp [hleft]
