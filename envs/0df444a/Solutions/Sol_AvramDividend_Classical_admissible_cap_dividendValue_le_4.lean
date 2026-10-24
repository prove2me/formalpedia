-- Prove2me | solution 4 for AvramDividend.Classical.admissible_cap_dividendValue_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:50:43.506149+00:00
-- url     : https://prove2.me/submissions/0f47e3e7-08e1-4111-a903-49ecdb71896e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissible_cap_dividendValue_le_bounded_variation
import Theorems.Thm_AvramDividend_Classical_admissible_cap_dividendValue_le_unbounded_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Obtain the common capped single-strategy verification inequality from
    the two distinct variation cases without importing a circular parent. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  by_cases hb : X.BoundedVariation
  · exact AvramDividend.Classical.admissible_cap_dividendValue_le_bounded_variation
      X hX hb q hq w C hC hw_cont hw0 hw_neg (hw_smooth.2 hb)
      hw_hjb x hx hxc D hD
  · exact AvramDividend.Classical.admissible_cap_dividendValue_le_unbounded_variation
      X hX hb q hq w C hC hw_cont hw0 hw_neg (hw_smooth.1 hb)
      hw_hjb x hx hxc D hD
