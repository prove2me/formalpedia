-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_negative_band_occupied_cell_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:17:35.015807+00:00
-- url     : https://prove2.me/submissions/37792dc4-2f0c-47d3-b9a5-15eeefa38114

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_shifted_negative_band_indicator_integral_eq_event_probability
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_occupied_cell_probability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original negative-band occupied-cell integral, including an arbitrary shift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (n : ℕ) :
    (let E : Set Ω := {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0}
     (∫⁻ ω, E.indicator (fun _ => (1 : ENNReal)) ω ∂P) =
       1 - P {ω : Ω |
         ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
         (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}) := by
  exact
    (avram_wave7_06_original_shifted_negative_band_indicator_integral_eq_event_probability
      X s T n).trans
      (avram_wave7_06_original_negative_band_occupied_cell_probability X s T n)
