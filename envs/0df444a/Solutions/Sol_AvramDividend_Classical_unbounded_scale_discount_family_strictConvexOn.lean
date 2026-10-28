-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_family_strictConvexOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:13:55.150672+00:00
-- url     : https://prove2.me/submissions/6f607b57-e975-466a-9960-a7a21709572a

import Mathlib.Analysis.Convex.Slope
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_convex_secants
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- At fixed positive reserve the q-scale family is strictly convex in discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q : ℝ, 0 ≤ q → IsScaleFunction X q (W q)) :
    ∀ x : ℝ, 0 < x →
      StrictConvexOn ℝ (Ici (0 : ℝ)) (fun q : ℝ => W q x) := by
  intro x hx
  apply strictConvexOn_of_slope_strict_mono_adjacent (convex_Ici (0 : ℝ))
  intro a b c ha hc hab hbc
  have hb : 0 ≤ b := le_trans ha hab.le
  exact unbounded_scale_discount_strict_convex_secants
    X hnbv a b c ha hb hc hab hbc
    (W a) (W b) (W c) (hW a ha) (hW b hb) (hW c hc) x hx
