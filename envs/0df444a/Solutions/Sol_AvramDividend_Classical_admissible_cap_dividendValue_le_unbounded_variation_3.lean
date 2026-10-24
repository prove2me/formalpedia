-- Prove2me | solution 3 for AvramDividend.Classical.admissible_cap_dividendValue_le_unbounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:42:56.639043+00:00
-- url     : https://prove2.me/submissions/78368c1b-8ae7-4d8b-8393-1dcbf633dceb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_truncated_dividend_payoff_measurable
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_truncated_bound_measurable
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_dividendValue_le_unbounded_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Passage from each closed finite-horizon dividend bound to the full
    discounted Stieltjes value via measurable monotone convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  apply AvramDividend.Classical.dividendValue_le_of_truncated_bound_measurable
    X q x D (ENNReal.ofReal (w x))
  · exact AvramDividend.Classical.truncated_dividend_payoff_measurable
      X q x D hD.1.1
  · intro n
    exact AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_unbounded_variation
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_hjb
      x hx hxc D hD (n : ℝ) (Nat.cast_nonneg n)
