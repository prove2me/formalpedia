-- Prove2me | solution 2 for AvramDividend.Classical.zero_cap_value_upper_bound_of_zero_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:02:49.35427+00:00
-- url     : https://prove2.me/submissions/55379625-1608-43bb-9684-a0189831cf8f

import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_above_cap
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_affine_nonnegative
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The cap-zero value bound extends from the origin by the initial lump sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hzero : valueFunctionLe X q 0 0 ≤
      ENNReal.ofReal (barrierValue W 0 0))
    (hval : 0 ≤ barrierValue W 0 0)
    (x : ℝ) (hx : 0 ≤ x) :
    valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by
  rcases eq_or_lt_of_le hx with hzero_x | hpos
  · subst x
    exact hzero
  · have hcap : valueFunctionLe X q 0 x =
        ENNReal.ofReal x + valueFunctionLe X q 0 0 := by
      simpa using (valueFunctionLe_above_cap X q x 0 le_rfl hpos)
    have hbar : barrierValue W 0 x = x + barrierValue W 0 0 :=
      barrierValue_zero_affine_nonnegative W x hx
    rw [hcap, hbar, ENNReal.ofReal_add hx hval]
    exact add_le_add_right hzero (ENNReal.ofReal x)
