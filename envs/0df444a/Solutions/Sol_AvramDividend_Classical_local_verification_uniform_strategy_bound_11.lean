-- Prove2me | solution 11 for AvramDividend.Classical.local_verification_uniform_strategy_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:45:43.872545+00:00
-- url     : https://prove2.me/submissions/c9cdfc42-c0a4-4754-b0a8-905fa390054d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit1_capped_value_eq_iSup_natural_ruin_stopped
import Theorems.Thm_AvramDividend_Classical_admissible_cap_nat_horizon_bound_bounded_variation
import Theorems.Thm_AvramDividend_Classical_admissible_cap_nat_horizon_bound_unbounded_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Original capped dividend-value bound from both natural-ruin horizon budgets. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxC : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  have hcap : valueFunctionLe X q C x ≤ ENNReal.ofReal (w x) := by
    rw [avram_limit1_capped_value_eq_iSup_natural_ruin_stopped X q C x]
    apply iSup_le
    intro E
    apply iSup_le
    intro hE
    apply iSup_le
    intro n
    by_cases hBV : X.BoundedVariation
    · exact admissible_cap_nat_horizon_bound_bounded_variation
        X hX hBV q hq w C hC hw_cont hw0 hw_neg
        (hw_smooth.2 hBV) hw_hjb x hx hxC E hE n
    · exact admissible_cap_nat_horizon_bound_unbounded_variation
        X hX hBV q hq w C hC hw_cont hw0 hw_neg
        (hw_smooth.1 hBV) hw_hjb x hx hxC E hE n
  have hThisLe : dividendValue X q x D ≤ valueFunctionLe X q C x := by
    unfold valueFunctionLe
    exact le_iSup_of_le D (le_iSup_of_le hD (le_refl _))
  exact hThisLe.trans hcap
