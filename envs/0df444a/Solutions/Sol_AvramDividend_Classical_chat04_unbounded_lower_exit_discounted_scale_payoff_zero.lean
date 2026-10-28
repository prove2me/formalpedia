-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_lower_exit_discounted_scale_payoff_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:18:08.129683+00:00
-- url     : https://prove2.me/submissions/631b3ef8-ffc6-414c-b85f-ce4ac94b24b2

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_lintegral_zero_of_Wzero
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Zero contribution of the lower boundary in the unbounded-variation branch. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) :
    (∫⁻ ω,
      if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0 ∂P) = 0 := by
  exact chat04_lower_exit_lintegral_zero_of_Wzero X q W hW
    (chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW) a x
