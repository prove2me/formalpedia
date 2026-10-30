-- Prove2me | solution 3 for AvramDividend.Classical.bounded_variation_stopped_scale_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:14:59.841495+00:00
-- url     : https://prove2.me/submissions/3f8268e7-85a2-42de-8d1f-8aba0e3d6080

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_stopped_scale_ost_payoff_balance
import Theorems.Thm_AvramDividend_Classical_chat03_exact_upperfirst_discount_integrand_measurable

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
  classical
  have hPay :=
    AvramDividend.Classical.bv_stopped_scale_ost_payoff_balance X hX q hq W hW hBV a x ha hx0 hxa
  have hMeas :=
    AvramDividend.Classical.chat03_exact_upperfirst_discount_integrand_measurable X (-x) (a - x) q
  have hfun : (fun ω : Ω => if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω
      then ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) * ENNReal.ofReal (W a) else 0)
      = (fun ω : Ω => (if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω
        then ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) else 0) * ENNReal.ofReal (W a)) := by
    funext ω
    by_cases h : twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω <;> simp [h]
  have hfac : (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω
      then ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) * ENNReal.ofReal (W a) else 0 ∂P)
      = ((∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω
        then ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) else 0 ∂P) * ENNReal.ofReal (W a)) := by
    rw [hfun]
    exact MeasureTheory.lintegral_mul_const _ hMeas
  calc (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a)
      = (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω
        then ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) else 0 ∂P) * ENNReal.ofReal (W a) := rfl
    _ = ENNReal.ofReal (W x) := by
        rw [← hfac]
        exact hPay
