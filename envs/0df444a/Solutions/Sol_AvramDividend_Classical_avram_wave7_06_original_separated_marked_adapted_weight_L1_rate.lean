-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_separated_marked_adapted_weight_L1_rate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:23:50.137988+00:00
-- url     : https://prove2.me/submissions/5c9ac8eb-7a3f-48ff-86cd-387048939520
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original Lévy source predictable weighted marked-cell intensity, including UBV. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (H : Ω → ℝ≥0∞)
    (hH : Measurable[𝓕 s] H)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) =
      (∫⁻ ω, H ω ∂P) * ((T : ℝ≥0∞) * X.ν B) := by
  have hst : s ≤ s + T := le_add_of_nonneg_right (by positivity)
  obtain ⟨F, hF, hExtract⟩ :=
    avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
      X s (s + T) hst B hB
  let N : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B)
  let Future : Ω → ℝ≥0∞ := fun ω =>
    F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)
  have hEqual (ω : Ω) : N ω = Future ω := hExtract ω
  have hWeighted : (∫⁻ ω, H ω * N ω ∂P) =
      ∫⁻ ω, H ω * Future ω ∂P := by
    apply lintegral_congr
    intro ω
    rw [hEqual ω]
  have hUnweighted : (∫⁻ ω, Future ω ∂P) =
      ∫⁻ ω, N ω ∂P := by
    apply lintegral_congr
    intro ω
    exact (hEqual ω).symm
  have hFactor : (∫⁻ ω, H ω * Future ω ∂P) =
      (∫⁻ ω, H ω ∂P) * (∫⁻ ω, Future ω ∂P) :=
    avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor
      X s H hH F hF
  have hRate : (∫⁻ ω, N ω ∂P) =
      (T : ℝ≥0∞) * X.ν B := by
    change (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) = _
    calc
      _ = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B) ∂P) :=
        avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
          X s T B hB
      _ = (T : ℝ≥0∞) * X.ν B :=
        avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
          X T B hB ε hε hBsep
  change (∫⁻ ω, H ω * N ω ∂P) =
    (∫⁻ ω, H ω ∂P) * ((T : ℝ≥0∞) * X.ν B)
  calc
    _ = (∫⁻ ω, H ω * Future ω ∂P) := hWeighted
    _ = (∫⁻ ω, H ω ∂P) * (∫⁻ ω, Future ω ∂P) := hFactor
    _ = (∫⁻ ω, H ω ∂P) * (∫⁻ ω, N ω ∂P) := by rw [hUnweighted]
    _ = (∫⁻ ω, H ω ∂P) * ((T : ℝ≥0∞) * X.ν B) := by rw [hRate]
