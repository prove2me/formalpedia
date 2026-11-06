-- Prove2me | solution 25 for AvramDividend.Classical.local_verification
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:52:13.969688+00:00
-- url     : https://prove2.me/submissions/217875b9-e43f-41a2-9933-d100c45d7dbf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_strategywise_cap_budget_to_both_values
import Theorems.Thm_AvramDividend_Classical_admissible_cap_dividendValue_le_bounded_variation
import Theorems.Thm_AvramDividend_Classical_admissible_cap_dividendValue_le_unbounded_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/- Direct original-process local verification from BV and UBV perpetual bounds. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  apply avram_sweep16_original_strategywise_cap_budget_to_both_values X q w C
  intro x hx hxc D hD
  by_cases hBV : X.BoundedVariation
  · exact admissible_cap_dividendValue_le_bounded_variation
      X hX hBV q hq w C hC hw_cont hw0 hw_neg
      (hw_smooth.2 hBV) hw_hjb x hx hxc D hD
  · exact admissible_cap_dividendValue_le_unbounded_variation
      X hX hBV q hq w C hC hw_cont hw0 hw_neg
      (hw_smooth.1 hBV) hw_hjb x hx hxc D hD
