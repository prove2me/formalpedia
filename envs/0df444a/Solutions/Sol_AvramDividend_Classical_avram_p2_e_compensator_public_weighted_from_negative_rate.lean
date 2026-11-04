-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_public_weighted_from_negative_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:09:05.884259+00:00
-- url     : https://prove2.me/submissions/dc5e566f-8b40-4ba4-b614-15801f407757

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_rate_from_unconditional

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Public original-source weighted marked compensation from an independently
established unconditional strictly negative Borel jump-rate identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (W : Ω → ℝ≥0∞) (hW : Measurable[𝓕 s] W)
    (hNegativeRate :
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ Iio (0 : ℝ))) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B ∩ Iio (0 : ℝ))) :
    (∫⁻ ω, W ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      (∫⁻ ω, W ω ∂P) *
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
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
  exact avram_p2_e_compensator_weighted_rate_from_unconditional
    X s t hst B hB W hW hFullRate
