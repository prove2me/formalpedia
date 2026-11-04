-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_public_event_from_negative_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:01:13.022678+00:00
-- url     : https://prove2.me/submissions/dae73981-74e9-4be4-bcbc-7e6912bce702

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_source_rectangle_of_future_extractor_and_unconditional_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- A public original-process past-event compensation bridge using only the
strictly negative marked unconditional rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNegativeRate :
      (∫⁻ ω,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ (B ∩ Iio (0 : ℝ))) ∂P) =
        ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B ∩ Iio (0 : ℝ))) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  let N : Ω → Set ℝ → ℝ≥0∞ := fun ω D =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ D)
  have hFullRate : (∫⁻ ω, N ω B ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
    calc
      (∫⁻ ω, N ω B ∂P) =
          (∫⁻ ω, N ω (B ∩ Iio (0 : ℝ)) ∂P) := by
        apply lintegral_congr_ae
        filter_upwards [] with ω
        exact avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
          X ω s t B hB
      _ = ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B ∩ Iio (0 : ℝ)) :=
        hNegativeRate
      _ = ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
        rw [← avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction
          X B hB]
  obtain ⟨F, hF, hExtract⟩ :=
    avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
      X s t hst B hB
  exact avram_wave7_01_actual_source_rectangle_of_future_extractor_and_unconditional_rate
    X s t hst A hA B hB F hF hExtract hFullRate
