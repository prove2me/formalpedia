-- Prove2me | solution 1 for AvramDividend.Classical.chat12_initial_record_trueExit_factor_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:17:03.20735+00:00
-- url     : https://prove2.me/submissions/0060c050-b063-462d-9dbb-3d5435f5fc85

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_weight_lower_of_strict_exit
import Theorems.Thm_AvramDividend_Classical_killed_lintegral_ofReal_scaled_lower

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ENNReal.ofReal ε *
      (∫⁻ ω, if twoSidedExitUpTime X ε ω <
          twoSidedExitDownTime X (ε - a) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X ε ω).toReal)))
      else 0 ∂P) ≤
      (∫⁻ ω,
        if twoSidedExitUpTime X ((1 : ℝ) * ε) ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (ε * Real.exp
            (-(q * (twoSidedExitUpTime X ((1 : ℝ) * ε) ω).toReal)))
        else 0 ∂P) := by
  have hKilled :=
    killed_firstRecord_weight_lower_of_strict_exit
      X a ε ha (le_of_lt hε)
      (fun ω => ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X ε ω).toReal))))
      (∫⁻ ω, if twoSidedExitUpTime X ε ω <
          twoSidedExitDownTime X (ε - a) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X ε ω).toReal)))
      else 0 ∂P) rfl
  have hScaled :
      ENNReal.ofReal ε *
        (∫⁻ ω, if twoSidedExitUpTime X ε ω <
          twoSidedExitDownTime X (ε - a) ω then
          ENNReal.ofReal (Real.exp
            (-(q * (twoSidedExitUpTime X ε ω).toReal)))
        else 0 ∂P) ≤
      ENNReal.ofReal ε *
        (∫⁻ ω, if twoSidedExitUpTime X ε ω < barrierRuinTime X a ω then
          ENNReal.ofReal (Real.exp
            (-(q * (twoSidedExitUpTime X ε ω).toReal)))
          else 0 ∂P) :=
    mul_le_mul_right hKilled (ENNReal.ofReal ε)
  calc
    _ ≤ ENNReal.ofReal ε *
        (∫⁻ ω, if twoSidedExitUpTime X ε ω < barrierRuinTime X a ω then
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
