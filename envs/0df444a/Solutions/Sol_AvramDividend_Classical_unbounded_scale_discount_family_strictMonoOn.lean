-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_family_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:00:07.884624+00:00
-- url     : https://prove2.me/submissions/3d7168e2-a8bb-482b-bc16-54ef457e66fc

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_monotone
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- At every strictly positive reserve, the q-scale family is strictly increasing in q. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q : ℝ, 0 ≤ q → IsScaleFunction X q (W q)) :
    ∀ x : ℝ, 0 < x →
      StrictMonoOn (fun q : ℝ => W q x) (Ici (0 : ℝ)) := by
  intro x hx
  intro a ha b hb hab
  exact unbounded_scale_discount_strict_monotone
    X hnbv a b ha hb hab (W a) (W b)
    (hW a ha) (hW b hb) x hx
