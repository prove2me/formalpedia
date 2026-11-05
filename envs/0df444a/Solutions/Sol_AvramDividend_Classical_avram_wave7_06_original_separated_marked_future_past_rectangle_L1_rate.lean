-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_separated_marked_future_past_rectangle_L1_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:17:27.136676+00:00
-- url     : https://prove2.me/submissions/a2baccbb-a529-428f-8092-a59d91b244b0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Genuine original-filtration future predictable rectangle compensation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (A : Set Ω)
    (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) =
      P A * ((T : ℝ≥0∞) * X.ν B) := by
  have hst : s ≤ s + T := le_add_of_nonneg_right (by positivity)
  obtain ⟨F, hF, hRep⟩ :=
    avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
      X s (s + T) hst B hB
  calc
    _ = P A * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s (s + T) ×ˢ B) ∂P) :=
      avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor
        X s (s + T) hst A hA B hB F hF hRep
    _ = P A * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B) ∂P) := by
      rw [avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
        X s T B hB]
    _ = P A * ((T : ℝ≥0∞) * X.ν B) := by
      rw [avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
        X T B hB ε hε hBsep]
