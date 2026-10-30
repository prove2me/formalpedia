-- Prove2me | solution 14 for AvramDividend.Classical.bv_stopped_scale_ost_payoff_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T14:35:40.64098+00:00
-- url     : https://prove2.me/submissions/1c67f121-ba7b-4e02-9aba-442af4a991ec

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_stopped_scale_ost_expectation_identity
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_lintegral_factorisation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Real killed BV stopped-scale expectation equals the actual discounted upper-first payoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω then
      ENNReal.ofReal (Real.exp
        (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
        ENNReal.ofReal (W a)
    else 0 ∂P) = ENNReal.ofReal (W x) := by
  have hPointwise (ω : Ω) :=
    chat04_strict_upper_exit_scale_payoff X W q a x hxa ω
  have hFactor :=
    chat04_strict_stopped_exit_payoff_lintegral_factorisation
      X q a x hxa W
  have hEquality :
      (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal (W a)
      else 0 ∂P) =
      (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂P) := by
    apply lintegral_congr_ae
    filter_upwards with ω
    exact (hPointwise ω).symm
  calc
    _ = twoSidedExitExpectation X q a x *
      ENNReal.ofReal (W a) := hEquality.trans hFactor
    _ = ENNReal.ofReal (W x) :=
      bv_stopped_scale_ost_expectation_identity X hX q hq W hW hBV
        a x ha hx0 hxa
