-- Prove2me | solution 2 for AvramDividend.Classical.bounded_variation_stopped_scale_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:59:07.489409+00:00
-- url     : https://prove2.me/submissions/291e541f-0665-49f6-86d0-3c3d5e36968d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_stopped_scale_ost_payoff_balance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by
  -- Single Open premise: the named-clock OST payoff balance (same binders).
  have hOST := AvramDividend.Classical.bv_stopped_scale_ost_payoff_balance
    X hX q hq W hW hBV a x ha hx0 hxa
  -- Raw ⨅ clocks fold to the named two-sided exit clocks (definitions).
  have hFold : (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) =
      (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal)))
      else 0 ∂P) := by
    unfold twoSidedExitUpTime twoSidedExitDownTime
    rfl
  -- Constant W a factors out of the named payoff integral.
  have hfactor : (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
        ENNReal.ofReal (W a)
    else 0 ∂P) =
      (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal)))
      else 0 ∂P) * ENNReal.ofReal (W a) := by
    have hpt : ∀ ω : Ω,
        (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
            ENNReal.ofReal (W a)
        else 0)
        = ((if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal)))
        else 0) * ENNReal.ofReal (W a)) := by
      intro ω
      by_cases h : twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω
      · simp [h]
      · simp [h]
    have hfun : (fun ω => if twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal (W a)
      else 0)
        = fun ω => (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal)))
        else 0) * ENNReal.ofReal (W a) :=
      funext (fun ω => hpt ω)
    rw [hfun, lintegral_mul_const']
    exact ENNReal.ofReal_ne_top
  rw [hFold, ← hfactor]
  exact hOST
