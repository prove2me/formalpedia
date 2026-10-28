-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_stopped_balance_iff_exit_ratio_any_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T13:05:08.157187+00:00
-- url     : https://prove2.me/submissions/b3ff40bd-e211-4236-9042-f4652e296242

import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_any_measure_factorisation
import Mathlib.Analysis.Complex.Exponential

set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true

/-- Arbitrary-measure stopped scale balance is equivalent to the strict upper-first ratio. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q a x : ℝ) (hxa : x ≤ a) (W : ℝ → ℝ) (hWa : 0 < W a) :
    ((∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) = ENNReal.ofReal (W x)) ↔
    ((∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) = ENNReal.ofReal (W x / W a)) := by
  have hden0 : ENNReal.ofReal (W a) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hWa)
  have hdenTop : ENNReal.ofReal (W a) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hFactor :=
    chat04_strict_stopped_exit_payoff_any_measure_factorisation
      X μ q a x hxa W
  constructor
  · intro hBalance
    have hMul : (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x) := hFactor.symm.trans hBalance
    have hRatio : (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) =
        ENNReal.ofReal (W x) / ENNReal.ofReal (W a) := by
      calc
        _ = ((∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) * ENNReal.ofReal (W a)) /
            ENNReal.ofReal (W a) := by
              symm
              exact ENNReal.mul_div_cancel_right hden0 hdenTop
        _ = ENNReal.ofReal (W x) / ENNReal.ofReal (W a) := by
              rw [hMul]
    simpa only [ENNReal.ofReal_div_of_pos hWa] using hRatio
  · intro hRatio
    calc
      (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) = (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) * ENNReal.ofReal (W a) := hFactor
      _ = ENNReal.ofReal (W x / W a) * ENNReal.ofReal (W a) := by
        rw [hRatio]
      _ = ENNReal.ofReal (W x) := by
        rw [ENNReal.ofReal_div_of_pos hWa]
        exact ENNReal.div_mul_cancel hden0 hdenTop
