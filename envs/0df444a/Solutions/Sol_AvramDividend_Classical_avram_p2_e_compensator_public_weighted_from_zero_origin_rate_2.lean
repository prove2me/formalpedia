-- Prove2me | solution 2 for AvramDividend.Classical.avram_p2_e_compensator_public_weighted_from_zero_origin_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:20:58.03939+00:00
-- url     : https://prove2.me/submissions/9f81cca3-b2f3-4b21-ab93-d41f767867af

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_public_reciprocal_borel_cover
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_zero_origin_all_real_source_rate
import Theorems.Thm_AvramDividend_Classical_avram_integration_original_unit_separated_negative_borel_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_source_borel_rate_from_separated_monotone_bands
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_public_weighted_from_negative_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Public arbitrary-weight original predictable rectangle compensation from
the genuine unit-horizon separated rate and Proved original time scaling. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (W : Ω → ℝ≥0∞) (hW : Measurable[𝓕 s] W) :
    (∫⁻ ω, W ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      (∫⁻ ω, W ω ∂P) *
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
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
    have hUnit :=
      avram_integration_original_unit_separated_negative_borel_levy_rate
        X (C n) (hCm n) ε hε hCsep
    have hScale :=
      avram_p2_d_future_original_zero_origin_all_real_source_rate
        X (C n) (hCm n) (t - s)
    rw [hUnit] at hScale
    exact hShift.trans hScale
  have hNegativeRate :=
    avram_wave7_01_source_borel_rate_from_separated_monotone_bands
      X s t hst (B ∩ Iio (0 : ℝ)) C hCm hCmono hCover hSep hBandRate
  exact avram_p2_e_compensator_public_weighted_from_negative_rate
    X s t hst B hB W hW hNegativeRate
