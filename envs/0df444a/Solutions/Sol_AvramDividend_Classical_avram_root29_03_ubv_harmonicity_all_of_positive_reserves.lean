-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_ubv_harmonicity_all_of_positive_reserves
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:52:59.889951+00:00
-- url     : https://prove2.me/submissions/1a72ffea-c9a0-4402-bfcb-2d7857c20222

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_stopped_scale_negative_reserve
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_stopped_scale_nonpositive_upper
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_stopped_scale_zero_reserve_of_near_zero
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_unbounded_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- All nonpositive-reserve cases of the true stopped-scale identity follow
from established original-Lévy boundary results. The remaining hypothesis
is exactly the true identity at every strictly positive reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hPositive : ∀ (a x : ℝ), 0 < x → x ≤ a →
      (∫⁻ ω, (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0) + (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) ∂P) = ENNReal.ofReal (W x)) :
    ∀ (a x : ℝ), x ≤ a →
      (∫⁻ ω, (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0) + (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) ∂P) = ENNReal.ofReal (W x) := by
  intro a x hxa
  by_cases ha : a ≤ 0
  · exact chat04_unbounded_stopped_scale_nonpositive_upper
      X hnbv q hq W hW a x hxa ha
  have haPos : 0 < a := lt_of_not_ge ha
  rcases lt_trichotomy x 0 with hxNeg | hxZero | hxPos
  · exact chat04_unbounded_stopped_scale_negative_reserve
      X hnbv q hq W hW a x hxa hxNeg
  · subst x
    simpa only [sub_zero, neg_zero, zero_add] using
      (chat04_unbounded_stopped_scale_zero_reserve_of_near_zero
        X hnbv q hq W hW a haPos
        (ae_negative_near_zero_of_unbounded_variation X hnbv))
  · exact hPositive a x hxPos hxa
