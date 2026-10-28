-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_family_continuousOn_all_reserves
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:37:35.004265+00:00
-- url     : https://prove2.me/submissions/7589371e-d060-4ce1-933e-fba5b113b338

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Topology.ContinuousOn
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_continuousOn
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- For every real reserve, q-scale values vary continuously in the discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q ∈ Icc (0 : ℝ) Q, IsScaleFunction X q (W q)) :
    ∀ x : ℝ, ContinuousOn (fun q : ℝ => W q x) (Icc (0 : ℝ) Q) := by
  intro x
  by_cases hx : 0 < x
  · exact unbounded_scale_discount_family_continuousOn X hnbv Q hQ W hW x hx
  · have hxle : x ≤ 0 := le_of_not_gt hx
    have hz : ∀ q ∈ Icc (0 : ℝ) Q, W q x = 0 := by
      intro q hq
      rcases lt_or_eq_of_le hxle with hneg | heq
      · exact (hW q hq).1 x hneg
      · subst x
        exact unbounded_scale_zero_origin_nonnegative_discount X hnbv q hq.1 (W q) (hW q hq)
    have hc : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc (0 : ℝ) Q) :=
      continuousOn_const
    exact hc.congr (by intro q hq; exact hz q hq)
