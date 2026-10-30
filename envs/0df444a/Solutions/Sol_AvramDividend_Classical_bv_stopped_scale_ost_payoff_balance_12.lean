-- Prove2me | solution 12 for AvramDividend.Classical.bv_stopped_scale_ost_payoff_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:45:36.715355+00:00
-- url     : https://prove2.me/submissions/8ee523da-9eec-45d2-b044-1d38f6a80db6

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

-- Payoff balance via Proved factorisation + Proved upcrossing value,
-- closed by the Open expectation identity 322217fe (coordinator-owned).
-- Variant e (2026-10-29): calc-chain architecture over variant-d rewrites.
-- Step 1 identifies the goal integrand (constant W a) with the factorisation
-- integrand (W (x + X stopped)) by symmetric AE congruence; step 2 applies
-- the Proved factorisation; step 3 closes with the Open expectation identity.
-- Mathematics unchanged from variant d; elaboration path distinct (calc vs rw).
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
  have hId :=
    AvramDividend.Classical.bv_stopped_scale_ost_expectation_identity
      X hX q hq W hW hBV a x ha hx0 hxa
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
