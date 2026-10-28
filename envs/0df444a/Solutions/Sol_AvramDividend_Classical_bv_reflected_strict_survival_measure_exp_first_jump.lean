-- Prove2me | solution 1 for AvramDividend.Classical.bv_reflected_strict_survival_measure_exp_first_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T19:04:54.287612+00:00
-- url     : https://prove2.me/submissions/f67f8944-c1e2-4838-a307-2535bd3d0654

import Theorems.Thm_AvramDividend_Classical_bv_reflected_ruin_strict_survival_eq_exp_first_jump
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.NNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ) (ht : 0 < t) :
    P {ω : Ω | ENNReal.ofReal t < barrierRuinTime X 0 ω} =
      ENNReal.ofReal
        (Real.exp (-(t * (X.ν (Iio (0 : ℝ))).toReal))) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hreal :
      P.real {ω : Ω | ENNReal.ofReal t < barrierRuinTime X 0 ω} =
        Real.exp (-(t * (X.ν (Iio (0 : ℝ))).toReal)) := by
    simpa only [ENNReal.ofReal, Real.coe_toNNReal _ ht.le] using
      bv_reflected_ruin_strict_survival_eq_exp_first_jump
        X hStanding hBV hFinite (Real.toNNReal t)
  have hnotTop :
      P {ω : Ω | ENNReal.ofReal t < barrierRuinTime X 0 ω} ≠ ∞ := by
    finiteness
  calc
    P {ω : Ω | ENNReal.ofReal t < barrierRuinTime X 0 ω} =
      ENNReal.ofReal
        (P.real {ω : Ω | ENNReal.ofReal t < barrierRuinTime X 0 ω}) :=
          (ENNReal.ofReal_toReal hnotTop).symm
    _ = ENNReal.ofReal
      (Real.exp (-(t * (X.ν (Iio (0 : ℝ))).toReal))) :=
        congrArg ENNReal.ofReal hreal
