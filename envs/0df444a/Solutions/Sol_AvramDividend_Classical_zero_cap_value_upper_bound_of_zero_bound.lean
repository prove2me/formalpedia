-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_value_upper_bound_of_zero_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:02:35.529986+00:00
-- url     : https://prove2.me/submissions/c6112f3a-0a3e-4ba3-bf81-fc9cc03cb06f

import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_above_cap
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_affine_nonnegative
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The zero-capped upper bound for all reserves follows from its reserve-zero instance. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hzero : valueFunctionLe X q 0 0 ≤
      ENNReal.ofReal (barrierValue W 0 0))
    (hval : 0 ≤ barrierValue W 0 0)
    (x : ℝ) (hx : 0 ≤ x) :
    valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by
  rcases eq_or_lt_of_le hx with hzeroEq | hpos
  · rw [← hzeroEq]
    exact hzero
  · have hsplit :
        valueFunctionLe X q 0 x =
          ENNReal.ofReal x + valueFunctionLe X q 0 0 := by
      simpa using valueFunctionLe_above_cap X q x 0 (le_refl 0) hpos
    calc
      valueFunctionLe X q 0 x =
          ENNReal.ofReal x + valueFunctionLe X q 0 0 := hsplit
      _ ≤ ENNReal.ofReal x + ENNReal.ofReal (barrierValue W 0 0) :=
        add_le_add_right hzero (ENNReal.ofReal x)
      _ = ENNReal.ofReal (x + barrierValue W 0 0) := by
        symm
        exact ENNReal.ofReal_add hx hval
      _ = ENNReal.ofReal (barrierValue W 0 x) := by
        rw [barrierValue_zero_affine_nonnegative W x hx]
