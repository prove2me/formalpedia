-- Prove2me | solution 13 for AvramDividend.Classical.bv_stopped_scale_ost_payoff_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:44:34.213391+00:00
-- url     : https://prove2.me/submissions/eb872fde-54cc-4280-801d-c82b8286759c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_lintegral_factorisation
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff
import Theorems.Thm_AvramDividend_Classical_bv_stopped_scale_ost_expectation_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

-- HELD DRAFT — DO NOT SUBMIT while 18149 is PENDING.
-- Variant f staging: isolates the Open closer 322217fe behind an explicit
-- `suffices` so a future CE diagnostic pinpoints factorisation/congruence vs
-- expectation-identity failure without re-editing under a pending duplicate.
-- Mathematics identical to variant e (calc chain); structure only.
-- ProofCheckpoint: MATHEMATICAL_DECOMPOSITION. No local Lean was run.
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
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
        ENNReal.ofReal (W a)
    else 0 ∂P) = ENNReal.ofReal (W x) := by
  have hPay : ∀ ω : Ω,
      (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0) =
      (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal (W a)
      else 0) :=
    fun ω =>
      AvramDividend.Classical.chat04_strict_upper_exit_scale_payoff
        X W q a x hxa ω
  have hcongr : (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω then
    ENNReal.ofReal
      (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
      ENNReal.ofReal
        (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
    else 0 ∂P) =
    (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω then
    ENNReal.ofReal
      (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
      ENNReal.ofReal (W a)
    else 0 ∂P) :=
    lintegral_congr_ae (Filter.Eventually.of_forall hPay)
  have hFac :=
    AvramDividend.Classical.chat04_strict_stopped_exit_payoff_lintegral_factorisation
      X q a x hxa W
  suffices hId : twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) from
    calc (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal (W a)
      else 0 ∂P)
        = (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
        else 0 ∂P) := hcongr.symm
      _ = twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) := hFac
      _ = ENNReal.ofReal (W x) := hId
  exact AvramDividend.Classical.bv_stopped_scale_ost_expectation_identity
    X hX q hq W hW hBV a x ha hx0 hxa
