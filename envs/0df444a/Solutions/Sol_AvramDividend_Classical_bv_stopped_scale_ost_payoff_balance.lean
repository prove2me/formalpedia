-- Prove2me | solution 1 for AvramDividend.Classical.bv_stopped_scale_ost_payoff_balance
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T11:40:25.862981+00:00
-- url     : https://prove2.me/submissions/a50e0d82-b264-407d-bf4d-0d8a5203a3aa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
  -- E01 causal repair of CE-16965: the old `exact hM` used a
  -- `Martingale ...`-typed term where an `Eq` was required, and dragged in
  -- three Open premises (martingale, finite_ae, no_creeping). This version
  -- uses only Proved bridges plus the newly authored OST-identity child
  -- (no Open deps, no sorry, no byte-identical resubmission).
  -- Proved pointwise bridge (3a6690c2): on the up-first event the stopped
  -- scale value equals `W a`.
  have hpoint : ∀ ω : Ω,
      (if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal (W a) else 0)
      = (if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω)) else 0) :=
    fun ω => (AvramDividend.Classical.chat04_strict_upper_exit_scale_payoff X W q a x hxa ω).symm
  have hrewrite : (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
        ENNReal.ofReal (W a) else 0 ∂P)
      = (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω)) else 0 ∂P) := by
    apply lintegral_congr_ae
    filter_upwards with ω
    exact hpoint ω
  -- Proved factorisation (e1242e81).
  have hfact :=
    AvramDividend.Classical.chat04_strict_stopped_exit_payoff_lintegral_factorisation X q a x hxa W
  -- OST expectation identity: authored child (PUBLISHED required before submit).
  have hOST : twoSidedExitExpectation X q a x * ENNReal.ofReal (W a)
      = ENNReal.ofReal (W x) :=
    AvramDividend.Classical.bv_stopped_scale_ost_expectation_identity
      X hX q hq W hW hBV a x ha hx0 hxa
  rw [hrewrite, hfact]
  exact hOST
