-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_predictable_negative_borel_rectangle_from_exhausting_halfline_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:10:39.833973+00:00
-- url     : https://prove2.me/submissions/660991df-ebe6-467b-affa-7bb3b262fee1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_any_start_separated_expected_mark_measure_exists_of_finite_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_any_start_mark_mean_measure_identification_from_halfline_tests
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_source_borel_rate_from_separated_monotone_bands
import Theorems.Thm_avram_wave7_01_predictable_all_negative_of_tests_identity_8e827326
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The genuine original past-event compensation extends from finite
negative half-line tests along a measurable exhaustion of the marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (D : Set ℝ) (hD : MeasurableSet D)
    (C : ℕ → Set ℝ) (hCm : ∀ n, MeasurableSet (C n))
    (hCmono : Monotone C) (hCover : (⋃ n, C n) = D)
    (hTests : ∀ n, ∃ ε : ℝ, 0 < ε ∧ C n ⊆ Iic (-ε) ∧
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) < ⊤ ∧
      ∀ a : ℝ,
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ (Iic a ∩ Iic (-ε))) ∂P) =
        (((t - s : ℝ≥0) : ℝ≥0∞)) * X.ν (Iic a ∩ Iic (-ε)))
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ D) ∂P) =
    P A * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν D) := by
  classical
  have hSep : ∀ n, ∃ ε : ℝ, 0 < ε ∧ C n ⊆ Iic (-ε) := by
    intro n
    obtain ⟨ε, hε, hC, hFinite, hHalfline⟩ := hTests n
    exact ⟨ε, hε, hC⟩
  have hBandRate : ∀ n,
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ C n) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞)) * X.ν (C n) := avram_wave7_01_predictable_all_negative_of_tests_identity_8e827326 (Ω := Ω) (mΩ := mΩ) (P := P) (𝓕 := 𝓕) (X := X) (s := s) (t := t) (hst := hst) (D := D) (hD := hD) (C := C) (hCm := hCm) (hCmono := hCmono) (hCover := hCover) (hTests := hTests) (A := A) (hA := hA) (hSep := hSep)
  have hDCount :=
    AvramDividend.Classical.avram_wave7_01_source_borel_rate_from_separated_monotone_bands
      X s t hst D C hCm hCmono hCover hSep hBandRate
  calc
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ D) ∂P) =
        P A * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ D) ∂P) :=
      AvramDividend.Classical.avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional
        X s t hst A hA D hD
    _ = _ := congrArg (fun z : ℝ≥0∞ => P A * z) hDCount
