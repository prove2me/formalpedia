-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys38_original_finite_simple_negative_mark_compensation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T12:38:34.762597+00:00
-- url     : https://prove2.me/submissions/5fd8c061-bba9-4ee5-af9f-9fa6c385d40a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_extractor_and_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_finite_simple_predictable_compensation_of_extractors

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Finite simple negative-mark compensation on the unchanged original source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (S : Finset ℕ) (s t : ℕ → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (H : ℕ → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ S, Measurable[𝓕 (s i)] (H i)) :
    (∫⁻ ω, ∑ i ∈ S, H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (t i) ×ˢ Iio (0 : ℝ)) ∂P) =
    ∑ i ∈ S,
      (∫⁻ ω, H i ω ∂P) *
        ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
  classical
  let F : ℕ → (ℝ≥0 → ℝ) → ℝ≥0∞ := fun i =>
    if hi : i ∈ S then
      Classical.choose
        (avram_wave7_01_original_intrinsic_marked_future_extractor_and_levy_rate
          X (s i) (t i) (hst i hi) (Iio (0 : ℝ)) measurableSet_Iio)
    else fun _ => 0
  have hFm (i : ℕ) (hi : i ∈ S) : Measurable (F i) := by
    simpa only [F, dif_pos hi] using
      (Classical.choose_spec
        (avram_wave7_01_original_intrinsic_marked_future_extractor_and_levy_rate
          X (s i) (t i) (hst i hi) (Iio (0 : ℝ)) measurableSet_Iio)).1
  have hExtract (i : ℕ) (hi : i ∈ S) (ω : Ω) :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ Iio (0 : ℝ)) =
        F i (fun v : ℝ≥0 => X.X (s i + v) ω - X.X (s i) ω) := by
    simpa only [F, dif_pos hi] using
      (Classical.choose_spec
        (avram_wave7_01_original_intrinsic_marked_future_extractor_and_levy_rate
          X (s i) (t i) (hst i hi) (Iio (0 : ℝ)) measurableSet_Iio)).2.1 ω
  exact avram_wave7_01_bv_finite_simple_predictable_compensation_of_extractors
    X hBV hFinite S s t hst H hH F hFm hExtract
