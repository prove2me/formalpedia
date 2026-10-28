-- Prove2me | solution 1 for AvramDividend.Classical.chat04_upper_exit_discount_integral_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:06:07.766517+00:00
-- url     : https://prove2.me/submissions/4f33920f-f984-476c-9d7a-14502ca0494d

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The killed successful upper-exit scale payoff is W(a) times the upper-first
discounted survival integral. No martingale or scale-function law is required.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (a x : ℝ) (hxa : x ≤ a) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂P) =
      (∫⁻ ω,
        if twoSidedExitUpTime X (a - x) ω <
            twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal (Real.exp
            (-(q * (twoSidedExitUpTime X (a - x) ω).toReal)))
        else 0 ∂P) * ENNReal.ofReal (W a) := by
  calc
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂P) =
      (∫⁻ ω,
        (if twoSidedExitUpTime X (a - x) ω <
             twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal (Real.exp
            (-(q * (twoSidedExitUpTime X (a - x) ω).toReal)))
        else 0) * ENNReal.ofReal (W a) ∂P) := by
      apply lintegral_congr
      intro ω
      rw [AvramDividend.Classical.chat04_strict_upper_exit_scale_payoff
        X W q a x hxa ω]
      by_cases h : twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω
      · simp [h]
      · simp [h]
    _ = _ := by
      exact lintegral_mul_const'
        (ENNReal.ofReal (W a))
        (fun ω : Ω =>
          if twoSidedExitUpTime X (a - x) ω <
              twoSidedExitDownTime X (-x) ω then
            ENNReal.ofReal (Real.exp
              (-(q * (twoSidedExitUpTime X (a - x) ω).toReal)))
          else 0)
        ENNReal.ofReal_ne_top
