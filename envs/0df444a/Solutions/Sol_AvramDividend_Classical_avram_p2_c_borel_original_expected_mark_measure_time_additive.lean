-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_original_expected_mark_measure_time_additive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:39:19.333603+00:00
-- url     : https://prove2.me/submissions/5962ce7a-6df5-464c-8509-be0c0309cd59

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_negative_mark_mean_measure
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_stationary_expected_mark_additive
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_general_time_mark_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Original intrinsic mark-count expectations admit additive elapsed-time
measure representatives, without identifying the unknown Lévy ν coefficient. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ μ : ℝ≥0 → Measure ℝ,
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        μ T B =
          (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 T ×ˢ B) ∂P)) ∧
      (∀ s t : ℝ≥0, μ (s + t) = μ s + μ t) := by
  classical
  let M : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  have hExists (T : ℝ≥0) :
      ∃ μT : Measure ℝ, ∀ B : Set ℝ, MeasurableSet B →
        μT B = (∫⁻ ω, M ω (Ioc 0 T ×ˢ B) ∂P) := by
    simpa only [M] using
      (avram_p2_a_zero_rate_original_negative_mark_mean_measure X T)
  let μ : ℝ≥0 → Measure ℝ := fun T => Classical.choose (hExists T)
  have hRep (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
      μ T B = (∫⁻ ω, M ω (Ioc 0 T ×ˢ B) ∂P) :=
    Classical.choose_spec (hExists T) B hB
  refine ⟨μ, ?_, ?_⟩
  · intro T B hB
    simpa only [M] using (hRep T B hB)
  · intro s t
    apply Measure.ext
    intro B hB
    have hMeas : Measurable (fun ω => M ω (Ioc 0 s ×ˢ B)) := by
      simpa only [M] using
        (avram_p2_d_future_intrinsic_general_time_mark_measurable
          X (Ioc 0 s ×ˢ B) (measurableSet_Ioc.prod hB))
    have hShift :
        (∫⁻ ω, M ω (Ioc s (s + t) ×ˢ B) ∂P) =
        (∫⁻ ω, M ω (Ioc 0 t ×ˢ B) ∂P) := by
      simpa only [M] using
        (avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
          X s t B hB)
    have hAdd :=
      avram_p2_c_borel_stationary_expected_mark_additive
        P M B hB s t hMeas hShift
    calc
      μ (s + t) B = (∫⁻ ω, M ω (Ioc 0 (s + t) ×ˢ B) ∂P) :=
        hRep (s + t) B hB
      _ = (∫⁻ ω, M ω (Ioc 0 s ×ˢ B) ∂P) +
          (∫⁻ ω, M ω (Ioc 0 t ×ˢ B) ∂P) := hAdd
      _ = μ s B + μ t B := by rw [hRep s B hB, hRep t B hB]
      _ = (μ s + μ t) B := by simp only [Measure.add_apply]
