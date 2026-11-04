-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_original_past_kernel_zero_origin_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:43:47.95969+00:00
-- url     : https://prove2.me/submissions/bdf3438c-9668-4371-9619-f075df617dce

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The exact measurable original future marked count has a past-event
conditional factorisation against the same zero-origin count mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      (∀ ω : Ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) = F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) ∧
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
        (∫⁻ ω in A, F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) ∂P) =
          P A * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (t - s) ×ˢ B) ∂P) := by
  obtain ⟨F, hF, hExtract⟩ :=
    avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
      X s t hst B hB
  refine ⟨F, hF, hExtract, ?_⟩
  intro A hA
  have hPast :=
    avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor
      X s t hst A hA B hB F hF hExtract
  have hend : s + (t - s) = t := add_tsub_cancel_of_le hst
  calc
    (∫⁻ ω in A, F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) ∂P) =
        (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) ∂P) := by
          apply lintegral_congr
          intro ω
          exact (hExtract ω).symm
    _ = P A * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) ∂P) := hPast
    _ = P A * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s (s + (t - s)) ×ˢ B) ∂P) := by
          rw [hend]
    _ = P A * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (t - s) ×ˢ B) ∂P) := by
          rw [avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
              X s (t - s) B hB]
