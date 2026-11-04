-- Prove2me | solution 4 for AvramDividend.Classical.avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:30:21.078697+00:00
-- url     : https://prove2.me/submissions/9e89dcfa-e61c-4b01-96c5-1d9b968dc165
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_negative_unit_to_original_past_kernel_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Import the verified original future-path kernel and reduce the canonical
predictable compensator to the existing genuine intrinsic unconditional rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  have hUnitNegative :
      ∀ (C : Set ℝ), MeasurableSet C →
      C ⊆ Iio (0 : ℝ) → (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (1 : ℝ≥0) ×ˢ C) ∂P) = X.ν C := by
    intro C hC hCneg
    have hr :=
      avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
        X (0 : ℝ≥0) (1 : ℝ≥0) (by simp) C hC
    simpa using hr
  obtain ⟨F, hF, hPath, hConditional⟩ :=
    avram_p2_d_future_negative_unit_to_original_past_kernel_levy_rate
      X s t hst B hB hUnitNegative
  calc
    _ = (∫⁻ ω in A,
      F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) ∂P) := by
        apply lintegral_congr_ae
        filter_upwards [] with ω
        exact hPath ω
    _ = _ := by simpa only [mul_assoc] using (hConditional A hA)
