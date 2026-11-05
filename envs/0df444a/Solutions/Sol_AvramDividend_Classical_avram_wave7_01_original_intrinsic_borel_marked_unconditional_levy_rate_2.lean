-- Prove2me | solution 2 for AvramDividend.Classical.avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:38:20.567297+00:00
-- url     : https://prove2.me/submissions/3759b528-7107-4830-895a-cb102cefda05

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_intrinsic_rate_restricted_nu_of_unit_separated_bands
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_negative_unit_mean_to_arbitrary_borel_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Deduce the general original Borel marked-rate theorem from the
separated-negative source rate, monotone measure extension, and the
proved stationary interval transfer. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  have hSeparated :
      ∀ (C : Set ℝ), MeasurableSet C →
        ∀ ε : ℝ, 0 < ε → C ⊆ Iic (-ε) →
          (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 (1 : ℝ≥0) ×ˢ C) ∂P) = X.ν C := by
    intro C hC ε hε hCsep
    simpa using
      (avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
        X (1 : ℝ≥0) C hC ε hε hCsep)
  have hUnitNegative :
      ∀ (C : Set ℝ), MeasurableSet C →
        C ⊆ Iio (0 : ℝ) →
          (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 (1 : ℝ≥0) ×ˢ C) ∂P) = X.ν C := by
    intro C hC hCneg
    have hRate :=
      avram_p2_c_borel_original_intrinsic_rate_restricted_nu_of_unit_separated_bands
        X hSeparated (1 : ℝ≥0) C hC
    have hEq : C ∩ Iio (0 : ℝ) = C := by
      ext x
      constructor
      · exact fun hx => hx.1
      · exact fun hx => ⟨hx, hCneg hx⟩
    simpa [hEq] using hRate
  exact avram_p2_d_future_negative_unit_mean_to_arbitrary_borel_rate
    X s t hst B hB hUnitNegative
