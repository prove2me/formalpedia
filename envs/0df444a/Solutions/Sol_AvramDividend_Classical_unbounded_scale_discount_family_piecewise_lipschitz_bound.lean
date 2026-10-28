-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_family_piecewise_lipschitz_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:00:36.777864+00:00
-- url     : https://prove2.me/submissions/9be34021-348b-4073-9082-eb4424871771

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_lipschitz_bound
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Explicit discount-modulus inequality across positive, zero and negative reserves. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q ∈ Icc (0 : ℝ) Q, IsScaleFunction X q (W q)) :
    ∀ x : ℝ, ∀ a ∈ Icc (0 : ℝ) Q, ∀ b ∈ Icc (0 : ℝ) Q,
      |W b x - W a x| ≤ |b - a| *
        (if 0 < x then ∫ s in Ioc (0 : ℝ) x, W Q s * W Q (x - s) else 0) := by
  intro x a ha b hb
  by_cases hx : 0 < x
  · simpa only [if_pos hx] using
      (unbounded_scale_discount_family_lipschitz_bound
        X hnbv Q hQ W hW x hx a ha b hb)
  · have hxle : x ≤ 0 := le_of_not_gt hx
    have hz : ∀ q ∈ Icc (0 : ℝ) Q, W q x = 0 := by
      intro q hq
      rcases lt_or_eq_of_le hxle with hneg | heq
      · exact (hW q hq).1 x hneg
      · subst x
        exact unbounded_scale_zero_origin_nonnegative_discount X hnbv q hq.1 (W q) (hW q hq)
    simp [hz a ha, hz b hb, hx]
