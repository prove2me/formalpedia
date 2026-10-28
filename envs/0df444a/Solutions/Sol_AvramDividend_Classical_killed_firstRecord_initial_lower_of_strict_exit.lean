-- Prove2me | solution 1 for AvramDividend.Classical.killed_firstRecord_initial_lower_of_strict_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:18:12.033186+00:00
-- url     : https://prove2.me/submissions/22644f2f-4bca-4cb7-abc6-01272224ebc2

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_weight_lower_of_strict_exit
import Theorems.Thm_AvramDividend_Classical_killed_lintegral_ofReal_scaled_lower

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

/-! Convert the ordinary strict q-scale exit into an actual paid first record. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (W : ℝ → ℝ)
    (hExit : (∫⁻ ω,
      if twoSidedExitUpTime X ε ω <
          twoSidedExitDownTime X (ε - a) ω
      then ENNReal.ofReal (Real.exp
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
    killed_firstRecord_weight_lower_of_strict_exit
      X a ε ha (le_of_lt hε)
      (fun ω => ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X ε ω).toReal))))
      (ENNReal.ofReal (W (a - ε) / W a)) hExit
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
