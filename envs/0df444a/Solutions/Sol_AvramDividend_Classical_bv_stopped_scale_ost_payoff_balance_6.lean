-- Prove2me | solution 6 for AvramDividend.Classical.bv_stopped_scale_ost_payoff_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:02:30.761992+00:00
-- url     : https://prove2.me/submissions/251ead0b-718e-4c0a-8fea-703ae5be482b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_lintegral_factorisation
import Theorems.Thm_AvramDividend_Classical_bv_stopped_scale_ost_expectation_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
        ENNReal.ofReal (W a)
    else 0 ∂P) = ENNReal.ofReal (W x) := by
  calc (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal (W a)
      else 0 ∂P)
      _ = (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂P) := by
        apply lintegral_congr_ae
        filter_upwards with ω
        exact (AvramDividend.Classical.chat04_strict_upper_exit_scale_payoff
          X W q a x hxa ω).symm
      _ = twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) :=
        AvramDividend.Classical.chat04_strict_stopped_exit_payoff_lintegral_factorisation
          X q a x hxa W
      _ = ENNReal.ofReal (W x) :=
        AvramDividend.Classical.bv_stopped_scale_ost_expectation_identity
          X hX q hq W hW hBV a x ha hx0 hxa
