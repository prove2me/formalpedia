-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_initial_dividendMeasure_atom_formula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:48:09.202507+00:00
-- url     : https://prove2.me/submissions/ebd0373d-34ab-4cca-91af-525962e075f8

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

/-- Exact initial dividend atom for all nonnegative initial capitals and barriers. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (ω : Ω) :
    dividendMeasure (barrierStrategy X x a) ω ({0} : Set ℝ) =
      ENNReal.ofReal (max 0 (x - a)) := by
  have hD : IsDividendStrategy 𝓕 (barrierStrategy X x a) :=
    barrierStrategy_isDividendStrategy_nonnegative_barrier X x a hx ha
  have hAtom :
      dividendMeasure (barrierStrategy X x a) ω ({0} : Set ℝ) =
        ENNReal.ofReal (rightLimit (barrierStrategy X x a) (0 : ℝ≥0) ω -
          barrierStrategy X x a (0 : ℝ≥0) ω) := by
    simpa using (dividendMeasure_singleton_eq_rightLimit_sub
      (barrierStrategy X x a) hD ω (0 : ℝ≥0))
  rw [hAtom, barrierStrategy_right_increment_formula X x a ω 0]
  simp
