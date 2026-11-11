-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys37_original_single_negative_mark_predictable_weight_compensation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T12:26:16.493886+00:00
-- url     : https://prove2.me/submissions/ebcd59e5-619f-4f5a-a61f-a3fe45d21697

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_extractor_and_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_negative_mark_adapted_weight_compensation_of_extractor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original measurable future-jump extractor discharges the compensation premise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iio (0 : ℝ)) ∂P) =
    (∫⁻ ω, H ω ∂P) *
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
  obtain ⟨F, hFm, hExtract, _⟩ :=
    avram_wave7_01_original_intrinsic_marked_future_extractor_and_levy_rate
      X s t hst (Iio (0 : ℝ)) measurableSet_Iio
  exact avram_wave7_01_bv_negative_mark_adapted_weight_compensation_of_extractor
    X hBV hFinite s t hst H hH F hFm hExtract
