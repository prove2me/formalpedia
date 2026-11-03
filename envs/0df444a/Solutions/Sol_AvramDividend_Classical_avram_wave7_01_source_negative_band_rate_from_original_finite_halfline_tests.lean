-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_source_negative_band_rate_from_original_finite_halfline_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:02:28.66731+00:00
-- url     : https://prove2.me/submissions/b2055437-e35e-4617-b069-711a9d739c4e


import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_any_start_separated_expected_mark_measure_exists_of_finite_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_any_start_mark_mean_measure_identification_from_halfline_tests
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_source_borel_rate_from_separated_monotone_bands
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (C : ℕ → Set ℝ) (hCm : ∀ n, MeasurableSet (C n))
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
    : ∀ n,
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ C n) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞)) * X.ν (C n) := by
    classical
    intro n
    obtain ⟨ε, hε, hC, hFinite, hHalfline⟩ := hTests n
    obtain ⟨μ, hFiniteμ, hμ⟩ :=
      AvramDividend.Classical.avram_wave7_01_original_any_start_separated_expected_mark_measure_exists_of_finite_mean
        X s t hst ε hε hFinite
    letI : IsFiniteMeasure μ := ⟨hFiniteμ⟩
    have hμTests : ∀ a : ℝ,
        μ (Iic a) = (((t - s : ℝ≥0) : ℝ≥0∞)) *
          X.ν (Iic a ∩ Iic (-ε)) := by
      intro a
      exact (hμ (Iic a) measurableSet_Iic).trans (hHalfline a)
    exact
      AvramDividend.Classical.avram_wave7_01_original_any_start_mark_mean_measure_identification_from_halfline_tests
        X s t hst ε hε μ hμ hμTests (C n) (hCm n) hC