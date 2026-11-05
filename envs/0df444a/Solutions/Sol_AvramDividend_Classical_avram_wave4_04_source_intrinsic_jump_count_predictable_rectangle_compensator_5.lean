-- Prove2me | solution 5 for AvramDividend.Classical.avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:02:16.089507+00:00
-- url     : https://prove2.me/submissions/8d39b1d0-a52b-4a39-be4f-261224b7a82b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_public_reciprocal_borel_cover
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_source_borel_rate_from_separated_monotone_bands
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_public_event_from_negative_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original predictable rectangle compensator reduces to the genuine
zero-origin separated negative marked Lévy rate through public lemmas. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  obtain ⟨C, hCm, hCmono, hCover, hSep⟩ :=
    avram_p2_e_compensator_public_reciprocal_borel_cover B hB
  let N : Ω → Set ℝ → ℝ≥0∞ := fun ω D =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ D)
  have hs : s + (t - s) = t := by
    calc
      s + (t - s) = (t - s) + s := add_comm _ _
      _ = t := tsub_add_cancel_of_le hst
  have hBandRate : ∀ n,
      (∫⁻ ω, N ω (C n) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C n) := by
    intro n
    obtain ⟨ε, hε, hCsep⟩ := hSep n
    have hShift :=
      avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
        X s (t - s) (C n) (hCm n)
    rw [hs] at hShift
    have hOrigin :=
      avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
        X (t - s) (C n) (hCm n) ε hε hCsep
    exact hShift.trans hOrigin
  have hNegativeRate :=
    avram_wave7_01_source_borel_rate_from_separated_monotone_bands
      X s t hst (B ∩ Iio (0 : ℝ)) C hCm hCmono hCover hSep hBandRate
  exact avram_p2_e_compensator_public_event_from_negative_rate
    X s t hst A hA B hB hNegativeRate
