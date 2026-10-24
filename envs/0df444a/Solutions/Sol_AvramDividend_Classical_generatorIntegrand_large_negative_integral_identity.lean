-- Prove2me | solution 1 for AvramDividend.Classical.generatorIntegrand_large_negative_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:24:55.869986+00:00
-- url     : https://prove2.me/submissions/bb74eaa2-2528-4d62-8435-6fb948c73bdc

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The generator's large negative jump integral is uncompensated. -/
theorem solution
    (w : ℝ → ℝ) (x : ℝ) (ν : Measure ℝ) :
    (∫ y in Iic (-1 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w x y ∂ν) =
      (∫ y in Iic (-1 : ℝ), w (x + y) - w x ∂ν) := by
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
  intro y hy
  change SpectrallyNegativeLevy.generatorIntegrand w x y = w (x + y) - w x
  exact generatorIntegrand_large_negative w x y hy
