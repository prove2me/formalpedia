-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_ubv_full_balance_of_positive_reserves
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:28:02.741144+00:00
-- url     : https://prove2.me/submissions/5b1cfd6b-c0b9-4872-be1a-4019c1e837ba

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_ubv_down_clock_immediate
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_zero_start_stopped_scale_of_down_exit_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Extend the genuine UBV discounted two-sided stopped balance from
strictly positive reserves to the zero-capital boundary. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hPositive : ∀ x : ℝ, 0 < x → x ≤ a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x)) :
    ∀ x : ℝ, 0 ≤ x → x ≤ a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x) := by
  intro x hx0 hxa
  rcases eq_or_lt_of_le hx0 with hzero | hxpos
  · subst x
    simpa only [twoSidedExitExpectation, twoSidedExitUpTime,
      twoSidedExitDownTime, sub_zero, neg_zero] using
      (chat04_unbounded_zero_start_stopped_scale_of_down_exit_zero
        X hnbv q hq W hW a ha
        (avram_root29_03_ubv_down_clock_immediate X hnbv))
  · exact hPositive x hxpos hxa
