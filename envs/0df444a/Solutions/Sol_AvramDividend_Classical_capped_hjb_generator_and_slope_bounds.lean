-- Prove2me | solution 1 for AvramDividend.Classical.capped_hjb_generator_and_slope_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:59:41.787985+00:00
-- url     : https://prove2.me/submissions/80e266a8-b2f7-43c2-852e-260cdef86615

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- HJB maximum zero forces the generator drift and dividend slope inequalities. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hHJB : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (y : ℝ) (hy : 0 < y) (hyC : ENNReal.ofReal y < C) :
    X.GeneratorIntegrable w y ∧
      X.generator w y ≤ q * w y ∧ 1 ≤ deriv w y := by
  obtain ⟨hIntegrable, hMax⟩ := hHJB y hy hyC
  have hGenerator : X.generator w y ≤ q * w y := by
    have hle : X.generator w y - q * w y ≤ 0 := by
      calc
        X.generator w y - q * w y ≤
            max (X.generator w y - q * w y) (1 - deriv w y) :=
          le_max_left _ _
        _ = 0 := hMax
    exact sub_nonpos.mp hle
  have hSlope : 1 ≤ deriv w y := by
    have hle : 1 - deriv w y ≤ 0 := by
      calc
        1 - deriv w y ≤
            max (X.generator w y - q * w y) (1 - deriv w y) :=
          le_max_right _ _
        _ = 0 := hMax
    exact sub_nonpos.mp hle
  exact ⟨hIntegrable, hGenerator, hSlope⟩
