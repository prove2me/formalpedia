-- Prove2me | solution 3 for AvramDividend.Classical.avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:07:05.28239+00:00
-- url     : https://prove2.me/submissions/38d850a0-32a1-4125-b675-192a6b2b7e5d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_original_signed_compact_intensity_eq_nu_tests
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_signed_tests_determine_negative_borel
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original-process all-horizon Lévy jump rate from source signed-test identification. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) ∂P) =
      (T : ℝ≥0∞) * X.ν B := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨σ, hRate, hSigned, hBand, hSupport, hSF⟩ :=
    avram_p2_a_assist_original_signed_compact_intensity_eq_nu_tests P X
  have hνBand : ∀ δ : ℝ, 0 < δ →
      (X.ν.restrict (Iio (0 : ℝ))) (Iic (-δ)) < ⊤ := by
    intro δ hδ
    have hsep : Iic (-δ) ⊆ Iio (0 : ℝ) := by
      intro y hy
      change y ≤ -δ at hy
      change y < 0
      linarith
    have hνfin : X.ν (Iic (-δ)) < ⊤ :=
      avram_p2_a_zero_rate_separated_borel_nu_finite
        X (Iic (-δ)) measurableSet_Iic δ hδ Subset.rfl
    calc
      (X.ν.restrict (Iio (0 : ℝ))) (Iic (-δ)) =
          X.ν (Iic (-δ) ∩ Iio (0 : ℝ)) :=
        Measure.restrict_apply measurableSet_Iic
      _ = X.ν (Iic (-δ)) :=
        congrArg X.ν (inter_eq_left.mpr hsep)
      _ < ⊤ := hνfin
  have hσB :
      σ B = (X.ν.restrict (Iio (0 : ℝ))) B :=
    avram_p2_a_assist_signed_tests_determine_negative_borel
      σ (X.ν.restrict (Iio (0 : ℝ)))
      hBand hνBand hSigned B hB ε hε hBsep
  have hNeg : B ⊆ Iio (0 : ℝ) := by
    intro y hy
    have hle : y ≤ -ε := hBsep hy
    change y < 0
    linarith
  have hνB : (X.ν.restrict (Iio (0 : ℝ))) B = X.ν B := by
    rw [Measure.restrict_apply hB, inter_eq_left.mpr hNeg]
  calc
    _ = (T : ℝ≥0∞) * σ B := hRate T B hB
    _ = (T : ℝ≥0∞) * X.ν B := by rw [hσB, hνB]
