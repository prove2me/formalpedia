-- Prove2me | solution 10 for AvramDividend.Classical.bv_stopped_scale_ost_payoff_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T06:17:16.458041+00:00
-- url     : https://prove2.me/submissions/4bb5b880-54c0-400b-8d12-633e4b2a31ff

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
-- hcongr identifies the goal integrand (constant W a) with the
-- factorisation integrand (W (x + X stopped)); hFac rewrites that to
-- twoSidedExitExpectation * W a; hId closes the balance.
-- Variant c (2026-10-29): pointwise leg via Proved 3a6690c2; drops inline hWval/rfl.
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
        (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
        ENNReal.ofReal (W a)
    else 0 ∂P) = ENNReal.ofReal (W x) := by
  have hFac :=
    AvramDividend.Classical.chat04_strict_stopped_exit_payoff_lintegral_factorisation
      X q a x hxa W
  -- Pointwise payoff identification via Proved bridge 3a6690c2
  -- (chat04_strict_upper_exit_scale_payoff): on the up-exit-first event the
  -- stopped payoff already equals its upper-barrier value. This replaces the
  -- inline hWval reconstruction (firstUpcrossing + coe_toNNReal + rfl unfold).
  have hPay : ∀ ω : Ω,
      (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0) =
      (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal (W a)
      else 0) :=
    fun ω =>
      AvramDividend.Classical.chat04_strict_upper_exit_scale_payoff
        X W q a x hxa ω
  have hcongr : (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω then
    ENNReal.ofReal
      (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
      ENNReal.ofReal
        (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
    else 0 ∂P) =
    (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω then
    ENNReal.ofReal
      (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
      ENNReal.ofReal (W a)
    else 0 ∂P) := by
    apply lintegral_congr_ae
    filter_upwards with ω
    exact hPay ω
  have hId :=
    AvramDividend.Classical.bv_stopped_scale_ost_expectation_identity
      X hX q hq W hW hBV a x ha hx0 hxa
  -- Split rewrites so a future diagnostic pinpoints the failing step:
  -- first identify the goal integral with the factorisation integrand,
  -- then rewrite that integral to expectation * W a.
  rw [← hcongr]
  rw [hFac]
  exact hId
