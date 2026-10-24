-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_no_initial_dividendMeasure_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:48:06.355469+00:00
-- url     : https://prove2.me/submissions/1fc88101-20b4-4906-9088-e93b544ceec4

import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_increment_formula
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Starting at or below the barrier produces no initial Stieltjes dividend atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hxa : x ≤ a) (ω : Ω) :
    dividendMeasure (barrierStrategy X x a) ω ({0} : Set ℝ) = 0 := by
  have hD : IsDividendStrategy 𝓕 (barrierStrategy X x a) :=
    barrierStrategy_isDividendStrategy_nonnegative_barrier X x a hx ha
  have hAtom :
      dividendMeasure (barrierStrategy X x a) ω ({0} : Set ℝ) =
        ENNReal.ofReal (rightLimit (barrierStrategy X x a) (0 : ℝ≥0) ω -
          barrierStrategy X x a (0 : ℝ≥0) ω) := by
    simpa using (dividendMeasure_singleton_eq_rightLimit_sub
      (barrierStrategy X x a) hD ω (0 : ℝ≥0))
  rw [hAtom, barrierStrategy_right_increment_formula X x a ω 0]
  have hnonpos : x - a ≤ 0 := sub_nonpos.mpr hxa
  simp [max_eq_left hnonpos]
