-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_initial_dividendMeasure_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:44:12.29107+00:00
-- url     : https://prove2.me/submissions/23d8aeb4-cab9-4f9f-a369-ab690f267ac3

import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_increment_formula

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The initial excess reserve is the atom of the dividend measure at time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hax : a < x) (ω : Ω) :
    dividendMeasure (barrierStrategy X x a) ω ({0} : Set ℝ) =
      ENNReal.ofReal (x - a) := by
  have hD : IsDividendStrategy 𝓕 (barrierStrategy X x a) :=
    barrierStrategy_isDividendStrategy_nonnegative_barrier X x a hx ha
  have hAtom :
      dividendMeasure (barrierStrategy X x a) ω ({0} : Set ℝ) =
        ENNReal.ofReal (rightLimit (barrierStrategy X x a) (0 : ℝ≥0) ω -
          barrierStrategy X x a (0 : ℝ≥0) ω) := by
    simpa using (dividendMeasure_singleton_eq_rightLimit_sub
      (barrierStrategy X x a) hD ω (0 : ℝ≥0))
  rw [hAtom, barrierStrategy_right_increment_formula X x a ω 0]
  have hpos : (0 : ℝ) ≤ x - a := sub_nonneg.mpr (le_of_lt hax)
  simp [max_eq_right hpos]
