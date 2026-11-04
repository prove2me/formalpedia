-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_adapted_from_past_event_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:44:00.144237+00:00
-- url     : https://prove2.me/submissions/acf5fb65-2e6f-4938-9951-5089272f82a3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_ambient_indicator_to_past_weight_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original Lévy marked rectangle event means transfer to adapted ENNReal
weights, explicitly conditional on the genuine event rectangle identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) (r : ℝ≥0∞)
    (hRect : ∀ A : Set Ω, MeasurableSet[𝓕 s] A →
      (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) = P A * r)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) =
    (∫⁻ ω, H ω ∂P) * r := by
  let N : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B)
  have hN : Measurable N :=
    avram_p2_f_weighted_original_intrinsic_rectangle_measurable X s T B hB
  change (∫⁻ ω, H ω * N ω ∂P) = (∫⁻ ω, H ω ∂P) * r
  exact avram_p2_f_weighted_ambient_indicator_to_past_weight_lintegral
    P N hN (𝓕 s) (𝓕.le s) r hRect H hH
