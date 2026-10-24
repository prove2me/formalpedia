-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_initial_atom_zero_iff_below_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:34:50.555459+00:00
-- url     : https://prove2.me/submissions/ac2deee8-2553-4b63-bce8-28e48abec6b9

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_initial_dividendMeasure_atom_formula
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Exactly the initial excess capital generates an atom of the dividend measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (ω : Ω) :
    dividendMeasure (barrierStrategy X x a) ω ({0} : Set ℝ) = 0 ↔
      x ≤ a := by
  rw [barrierStrategy_initial_dividendMeasure_atom_formula X x a hx ha ω]
  rw [ENNReal.ofReal_eq_zero]
  simp only [max_le_iff, le_refl, true_and]
  exact sub_nonpos
