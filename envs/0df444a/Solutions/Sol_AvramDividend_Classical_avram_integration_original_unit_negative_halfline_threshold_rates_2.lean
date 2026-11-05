-- Prove2me | solution 2 for AvramDividend.Classical.avram_integration_original_unit_negative_halfline_threshold_rates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:14:33.245089+00:00
-- url     : https://prove2.me/submissions/0ae770d7-09b1-4058-a8cf-b6f7f1e5a2ad

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The accepted original all-horizon count identity implies both negative halfline cutoffs. -/
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
  constructor
  · have h := avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
      X (1 : ℝ≥0) (Iic (-ε)) measurableSet_Iic ε hε Subset.rfl
    simpa using h
  · intro a ha
    have hδ : 0 < -a := by linarith
    have hsep : Iic a ⊆ Iic (-(-a)) := by
      simpa using (Subset.rfl : Iic a ⊆ Iic a)
    have h := avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
      X (1 : ℝ≥0) (Iic a) measurableSet_Iic (-a) hδ hsep
    simpa using h
