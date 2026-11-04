-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_negative_unit_to_original_past_kernel_levy_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:45:00.354421+00:00
-- url     : https://prove2.me/submissions/9c219afc-ff97-4932-a741-f6ae633456fb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_past_kernel_all_real_source_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_negative_unit_mean_to_arbitrary_borel_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Negative Borel unit-time Lévy identification suffices for the genuine
measurable future kernel and every original past-event ν-rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hunitNegative : ∀ (C : Set ℝ), MeasurableSet C →
      C ⊆ Iio (0 : ℝ) → (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (1 : ℝ≥0) ×ˢ C) ∂P) = X.ν C) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      (∀ ω : Ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) =
        F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) ∧
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
        (∫⁻ ω in A, F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) ∂P) =
          P A * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
  have hunitB : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) = X.ν B := by
    simpa using
      (avram_p2_d_future_negative_unit_mean_to_arbitrary_borel_rate
        X (0 : ℝ≥0) (1 : ℝ≥0) (by norm_num) B hB hunitNegative)
  rcases avram_p2_d_future_original_past_kernel_all_real_source_rate
    X s t hst B hB with ⟨F, hF, hExact, hPast⟩
  refine ⟨F, hF, hExact, ?_⟩
  intro A hA
  simpa only [hunitB] using (hPast A hA)
