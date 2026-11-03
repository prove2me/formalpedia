-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_source_predictable_separated_rectangle_of_halfline_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:55:22.886581+00:00
-- url     : https://prove2.me/submissions/cc9f9452-a83f-4efd-bb4c-d26b9d76d4f4


import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_any_start_separated_expected_mark_measure_exists_of_finite_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_any_start_mark_mean_measure_identification_from_halfline_tests
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Genuine original predictable compensation reduced to finite negative halfline intensity tests. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (ε : ℝ) (hε : 0 < ε)
    (hFiniteMean :
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) < ⊤)
    (hHalfline : ∀ a : ℝ,
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (Iic a ∩ Iic (-ε))) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞)) * X.ν (Iic a ∩ Iic (-ε)))
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBsep : B ⊆ Iic (-ε)) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      P A * ((((t - s : ℝ≥0) : ℝ≥0∞)) * X.ν B) := by
  classical
  obtain ⟨μ, hFiniteμ, hμ⟩ :=
    AvramDividend.Classical.avram_wave7_01_original_any_start_separated_expected_mark_measure_exists_of_finite_mean
      X s t hst ε hε hFiniteMean
  letI : IsFiniteMeasure μ := ⟨hFiniteμ⟩
  have hμTests : ∀ a : ℝ,
      μ (Iic a) = (((t - s : ℝ≥0) : ℝ≥0∞)) *
        X.ν (Iic a ∩ Iic (-ε)) := by
    intro a
    calc
      μ (Iic a) =
          (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc s t ×ˢ (Iic a ∩ Iic (-ε))) ∂P) :=
        hμ (Iic a) measurableSet_Iic
      _ = _ := hHalfline a
  have hRate :=
    AvramDividend.Classical.avram_wave7_01_original_any_start_mark_mean_measure_identification_from_halfline_tests
      X s t hst ε hε μ hμ hμTests B hB hBsep
  calc
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) ∂P) =
        P A * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) ∂P) :=
      AvramDividend.Classical.avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional
        X s t hst A hA B hB
    _ = _ := congrArg (fun z : ℝ≥0∞ => P A * z) hRate