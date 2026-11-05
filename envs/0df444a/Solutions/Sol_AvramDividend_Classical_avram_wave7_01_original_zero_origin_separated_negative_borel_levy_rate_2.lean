-- Prove2me | solution 2 for AvramDividend.Classical.avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:59:58.952277+00:00
-- url     : https://prove2.me/submissions/e994b8a4-4328-4ff2-babd-5dbeeebf13c1

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_integration_original_unit_separated_negative_borel_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_intrinsic_rate_restricted_nu_of_unit_separated_bands

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original all-horizon negative-band rate follows from the genuine
unit-horizon source rate and P2-C's all-time intrinsic measure scaling. -/
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
  have hUnit : ∀ C : Set ℝ, MeasurableSet C →
      ∀ δ : ℝ, 0 < δ → C ⊆ Iic (-δ) →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ C) ∂P) = X.ν C := by
    intro C hC δ hδ hCsep
    exact avram_integration_original_unit_separated_negative_borel_levy_rate
      X C hC δ hδ hCsep
  have hNegative : B ⊆ Iio (0 : ℝ) := by
    intro x hx
    exact lt_of_le_of_lt (hBsep hx) (neg_lt_zero.mpr hε)
  have hCap : B ∩ Iio (0 : ℝ) = B := by
    ext x
    constructor
    · exact fun hx => hx.1
    · exact fun hx => ⟨hx, hNegative hx⟩
  have hAll :=
    avram_p2_c_borel_original_intrinsic_rate_restricted_nu_of_unit_separated_bands
      X hUnit T B hB
  rw [hCap] at hAll
  exact hAll
