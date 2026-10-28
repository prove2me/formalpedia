-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_family_monotoneOn_all_reserves
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:38:54.459981+00:00
-- url     : https://prove2.me/submissions/921bed2a-0ce3-4cd9-b60c-e46402683b79

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Order.Monotone.Defs
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_strictMonoOn
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The full real-line q-scale family is nondecreasing in nonnegative q. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q : ℝ, 0 ≤ q → IsScaleFunction X q (W q)) :
    ∀ x : ℝ, MonotoneOn (fun q : ℝ => W q x) (Ici (0 : ℝ)) := by
  intro x
  by_cases hx : 0 < x
  · exact (unbounded_scale_discount_family_strictMonoOn X hnbv W hW x hx).monotoneOn
  · have hxle : x ≤ 0 := le_of_not_gt hx
    have hz : ∀ q : ℝ, 0 ≤ q → W q x = 0 := by
      intro q hq
      rcases lt_or_eq_of_le hxle with hneg | heq
      · exact (hW q hq).1 x hneg
      · subst x
        exact unbounded_scale_zero_origin_nonnegative_discount X hnbv q hq (W q) (hW q hq)
    intro a ha b hb hab
    change W a x ≤ W b x
    rw [hz a ha, hz b hb]
