-- Prove2me | solution 1 for AvramDividend.Classical.avram_integration_original_unit_negative_halfline_threshold_rates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:35:32.729375+00:00
-- url     : https://prove2.me/submissions/3589cba9-5927-4db5-b529-22faab1a21e7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_integration_original_unit_expected_mark_cutoff_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_compact_test_to_separated_borel_rate
import Theorems.Thm_AvramDividend_Classical_avram_integration_original_unit_expected_mark_compact_cutoff_tests

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original threshold rates from a finite genuine mean measure and Cc equality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ Iic (-ε)) ∂P) = X.ν (Iic (-ε)) ∧
    ∀ a : ℝ, a < -ε →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ Iic a) ∂P) = X.ν (Iic a) := by
  obtain ⟨ρ, hρ, hρfinite⟩ :=
    avram_integration_original_unit_expected_mark_cutoff_finite X ε hε
  have hρfinite' : (ρ.restrict (Iic (-ε))) Set.univ < ⊤ := by
    simpa using (lt_top_iff_ne_top.mpr hρfinite)
  letI : IsFiniteMeasure (ρ.restrict (Iic (-ε))) := ⟨hρfinite'⟩
  have hRegρ : (ρ.restrict (Iic (-ε))).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hTests :=
    avram_integration_original_unit_expected_mark_compact_cutoff_tests
      X ε hε ρ hρ hρfinite
  have hRate :=
    avram_p2_d_future_original_compact_test_to_separated_borel_rate
      X ε hε ρ hρ hRegρ hTests
  constructor
  · exact hRate (Iic (-ε)) measurableSet_Iic (Subset.rfl)
  · intro a ha
    exact hRate (Iic a) measurableSet_Iic
      (Iic_subset_Iic.mpr (le_of_lt ha))
