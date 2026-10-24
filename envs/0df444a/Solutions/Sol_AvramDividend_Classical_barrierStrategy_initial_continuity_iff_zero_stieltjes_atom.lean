-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_initial_continuity_iff_zero_stieltjes_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:44:03.825276+00:00
-- url     : https://prove2.me/submissions/66960752-3e61-4bea-ae82-63f9440774cb

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_initial_atom_zero_iff_below_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_of_le
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_not_right_continuous_at_zero_above_barrier
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- An initial Stieltjes dividend atom is equivalent to failing right continuity at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (ω : Ω) :
    ContinuousWithinAt
      (fun s => barrierStrategy X x a s ω) (Ici (0 : ℝ≥0)) 0 ↔
      dividendMeasure (barrierStrategy X x a) ω ({0} : Set ℝ) = 0 := by
  rw [barrierStrategy_initial_atom_zero_iff_below_barrier X x a hx ha ω]
  constructor
  · intro hc
    by_contra hxa
    exact (barrierStrategy_not_right_continuous_at_zero_above_barrier
      X x a ha (lt_of_not_ge hxa) ω) hc
  · intro hxa
    exact barrierStrategy_right_continuous_of_le X x a hxa ω 0
