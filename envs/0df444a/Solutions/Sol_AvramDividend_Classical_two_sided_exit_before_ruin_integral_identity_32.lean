-- Prove2me | solution 32 for AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T22:17:26.183668+00:00
-- url     : https://prove2.me/submissions/7be2dece-026f-441b-95d7-79d0f9b7b0bd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_bv_stopped_scale_ost_expectation_identity
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_expectation_scale_identity
import Theorems.Thm_AvramDividend_Classical_chat04_exit_ratio_of_stopped_balance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) =
      ENNReal.ofReal (W x / W a) := by
  have hBal : twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) = ENNReal.ofReal (W x) := by
    by_cases hBV : X.BoundedVariation
    · exact AvramDividend.Classical.bv_stopped_scale_ost_expectation_identity X hX q hq W hW hBV a x ha hx0 hxa
    · exact AvramDividend.Classical.chat04_unbounded_two_sided_exit_expectation_scale_identity X q hq W hW hBV a x ha hx0 hxa
  have hRatio : twoSidedExitExpectation X q a x = ENNReal.ofReal (W x / W a) := AvramDividend.Classical.chat04_exit_ratio_of_stopped_balance X hX q hq W hW a x ha hx0 hxa hBal
  unfold twoSidedExitExpectation twoSidedExitUpTime twoSidedExitDownTime at hRatio
  exact hRatio
