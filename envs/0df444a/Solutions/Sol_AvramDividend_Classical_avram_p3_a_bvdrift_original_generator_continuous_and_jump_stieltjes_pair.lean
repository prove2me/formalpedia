-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_generator_continuous_and_jump_stieltjes_pair
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:46:40.669851+00:00
-- url     : https://prove2.me/submissions/9b700e42-9686-47a7-b28e-29a16d9a68d4

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_residual_atomless_stieltjes_measure
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_stieltjes_function
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_leftLim_strict
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_real_jump_total_endpoint_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original generator and source-jump / continuous Stieltjes measures. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    (X.generator w x = X.drift * deriv w x +
      ∫ y in Iio (0 : ℝ), w (x + y) - w x ∂X.ν) ∧
    (∀ᵐ ω ∂P, ∃ μr μj : Measure ℝ≥0,
      (∀ a b : ℝ≥0, a ≤ b → μr (Ioc a b) = ENNReal.ofReal (
        ((((b : ℝ) * X.drift - X.X b ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) -
        (((a : ℝ) * X.drift - X.X a ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))))) ∧
      (∀ a : ℝ≥0, μr {a} = 0) ∧
      (∀ a b : ℝ≥0, a ≤ b → μj (Ioc a b) = ENNReal.ofReal (
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))) ∧
      (∀ t : ℝ≥0, 0 < t → μj {t} = ENNReal.ofReal
        (Function.leftLim (fun z : ℝ≥0 => X.X z ω) t - X.X t ω))) := by
  constructor
  · exact boundedVariation_generator_physical_drift_representation X hBV w x hGen
  · filter_upwards
      [avram_p3_a_bvdrift_original_raw_residual_atomless_stieltjes_measure X hBV,
        avram_p3_a_bvdrift_original_raw_jump_stieltjes_function X hBV,
        avram_p3_a_bvdrift_original_raw_jump_cumulative_leftLim_strict X hBV,
        avram_p3_a_bvdrift_original_raw_real_jump_total_endpoint_split X hBV]
      with ω hres hFexists hleft hsplit
    obtain ⟨μr, hμr, hatomr⟩ := hres
    obtain ⟨F, hFeq⟩ := hFexists
    refine ⟨μr, F.measure, hμr, hatomr, ?_, ?_⟩
    · intro a b hab
      simpa only [hFeq a, hFeq b] using (F.measure_Ioc a b)
    · intro t ht
      have hF_eq : (F : ℝ≥0 → ℝ) = (fun s : ℝ≥0 =>
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) :=
        funext hFeq
      have hleftF : Function.leftLim (F : ℝ≥0 → ℝ) t =
          (∑' u : ℝ≥0, if 0 < u ∧ u < t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by
        rw [hF_eq]
        exact hleft t ht
      rw [F.measure_singleton, hFeq t, hleftF, hsplit t ht]
      congr 1
      ring
