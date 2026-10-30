-- Prove2me | solution 2 for AvramDividend.Classical.bv_stopped_scale_ost_payoff_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T12:16:19.915385+00:00
-- url     : https://prove2.me/submissions/378a5e23-3192-4f0f-a799-72d49914e5ac

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_lintegral_factorisation
import Theorems.Thm_AvramDividend_Classical_bv_stopped_scale_ost_expectation_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

-- Sketch for 09caed2c (Open): BV stopped-scale OST payoff balance.
-- ProofCheckpoint: DIRECT_CANDIDATE (honest sketch via Open child).
-- Principal argument: the named-time payoff integral factors through the
-- two-sided exit expectation, which the Open child closes.
--   (1) Proved 3a6690c2 (pointwise payoff identification): at the up-exit
--       time, W (x + X_tau) = W a, so the W a integrand equals the W-form
--       integrand pointwise; lintegral_congr lifts this under the integral.
--   (2) Proved e1242e81 (payoff lintegral factorisation): the W-form
--       integral equals twoSidedExitExpectation X q a x * ofReal (W a).
--   (3) Open 322217fe (bv_stopped_scale_ost_expectation_identity): the
--       expectation balance, giving ofReal (W x).
-- Honest-sketch contract: step (3) cites an Open theorem, so at most
-- SKETCH_ACCEPTED is expected until 322217fe is discharged. Remote Prove2Me
-- alone decides validity. No local Lean was run.
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
  have hcong : (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal (W a)
      else 0 ∂P)
      = (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂P) := by
    apply lintegral_congr
    intro ω
    exact (AvramDividend.Classical.chat04_strict_upper_exit_scale_payoff
      X W q a x hxa ω).symm
  have hfact : (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂P)
      = twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) :=
    AvramDividend.Classical.chat04_strict_stopped_exit_payoff_lintegral_factorisation
      X q a x hxa W
  have hchild : twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) :=
    AvramDividend.Classical.bv_stopped_scale_ost_expectation_identity
      X hX q hq W hW hBV a x ha hx0 hxa
  calc (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal (W a)
      else 0 ∂P)
      = (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂P) := hcong
    _ = twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) := hfact
    _ = ENNReal.ofReal (W x) := hchild
