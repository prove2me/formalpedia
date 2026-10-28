-- Prove2me | solution 1 for AvramDividend.Classical.killed_firstRecord_initial_lower_of_raw_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:15:39.824971+00:00
-- url     : https://prove2.me/submissions/c689adec-9339-4457-908a-2a6fbf9e02f5

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_named_killed_upcrossing_lower_of_raw_exit
import Theorems.Thm_AvramDividend_Classical_killed_lintegral_ofReal_scaled_lower

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
/-! The two-sided exit identity supplies the scaled first surviving record. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (W : ℝ → ℝ)
    (hRaw : (∫⁻ ω,
      if twoSidedExitUpTime X ε ω ≠ ∞ ∧
          (∀ t : ℝ≥0, t < (twoSidedExitUpTime X ε ω).toNNReal →
            ε - a ≤ X.X t ω) then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X ε ω).toReal)))
      else 0 ∂P) =
      ENNReal.ofReal (W (a - ε) / W a)) :
    ENNReal.ofReal (ε * (W (a - ε) / W a)) ≤
      (∫⁻ ω,
        if twoSidedExitUpTime X ((1 : ℝ) * ε) ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (ε * Real.exp
            (-(q * (twoSidedExitUpTime X ((1 : ℝ) * ε) ω).toReal)))
        else 0 ∂P) := by
  have hKilled :=
    named_killed_upcrossing_lower_of_raw_exit
      X a ε ha (le_of_lt hε)
      (fun ω => ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X ε ω).toReal))))
      (ENNReal.ofReal (W (a - ε) / W a)) hRaw
  have hScaled :
      ENNReal.ofReal ε * ENNReal.ofReal (W (a - ε) / W a) ≤
      ENNReal.ofReal ε *
        (∫⁻ ω,
          if twoSidedExitUpTime X ε ω < barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp
              (-(q * (twoSidedExitUpTime X ε ω).toReal)))
          else 0 ∂P) :=
    mul_le_mul_right hKilled (ENNReal.ofReal ε)
  calc
    ENNReal.ofReal (ε * (W (a - ε) / W a)) =
        ENNReal.ofReal ε * ENNReal.ofReal (W (a - ε) / W a) :=
      ENNReal.ofReal_mul (le_of_lt hε)
    _ ≤ ENNReal.ofReal ε *
        (∫⁻ ω,
          if twoSidedExitUpTime X ε ω < barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp
              (-(q * (twoSidedExitUpTime X ε ω).toReal)))
          else 0 ∂P) := hScaled
    _ = (∫⁻ ω,
        ENNReal.ofReal ε *
          (if twoSidedExitUpTime X ε ω < barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp
              (-(q * (twoSidedExitUpTime X ε ω).toReal)))
          else 0) ∂P) :=
      (lintegral_const_mul' (ENNReal.ofReal ε)
        (fun ω => if twoSidedExitUpTime X ε ω < barrierRuinTime X a ω then
          ENNReal.ofReal (Real.exp
            (-(q * (twoSidedExitUpTime X ε ω).toReal)))
        else 0) (by simp)).symm
    _ = (∫⁻ ω,
        if twoSidedExitUpTime X ((1 : ℝ) * ε) ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (ε * Real.exp
            (-(q * (twoSidedExitUpTime X ((1 : ℝ) * ε) ω).toReal)))
        else 0 ∂P) := by
      apply lintegral_congr
      intro ω
      by_cases h : twoSidedExitUpTime X ε ω < barrierRuinTime X a ω
      · simp only [one_mul, if_pos h]
        exact (ENNReal.ofReal_mul (le_of_lt hε)).symm
      · simp only [one_mul, if_neg h, mul_zero]
