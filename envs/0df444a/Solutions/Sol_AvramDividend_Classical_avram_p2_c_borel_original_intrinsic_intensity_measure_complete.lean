-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_original_intrinsic_intensity_measure_complete
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:27:00.082615+00:00
-- url     : https://prove2.me/submissions/2db3add1-6238-4a13-aa6f-5742df2e3281

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_expected_measure_sigma_finite_additive_package
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_zero_origin_all_real_source_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original path has its own rigorous negative, sigma-finite jump
intensity: its unit-time expected marked-count measure. Identifying this
measure with the prescribed Lévy ν is a separate analytic obligation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ markRate : Measure ℝ,
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 T ×ˢ B) ∂P) = (T : ℝ≥0∞) * markRate B) ∧
      (∀ ε : ℝ, 0 < ε → markRate (Iic (-ε)) < ⊤) ∧
      (∀ (B : Set ℝ), MeasurableSet B →
        markRate B = markRate (B ∩ Iio (0 : ℝ))) ∧
      SigmaFinite markRate := by
  obtain ⟨μ, hRep, _, hFinite, hNegative, hSigma⟩ :=
    avram_p2_c_borel_original_expected_measure_sigma_finite_additive_package X
  refine ⟨μ 1, ?_, hFinite, ?_, hSigma 1⟩
  · intro T B hB
    calc
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 T ×ˢ B) ∂P) =
          (T : ℝ≥0∞) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) :=
            avram_p2_d_future_original_zero_origin_all_real_source_rate
              X B hB T
      _ = (T : ℝ≥0∞) * μ 1 B := by rw [← hRep 1 B hB]
  · intro B hB
    exact hNegative 1 B hB
