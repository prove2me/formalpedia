-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_initial_atom_positive_iff_above_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:58:53.350848+00:00
-- url     : https://prove2.me/submissions/6e2f8e7f-785c-462f-a05e-f1780521a2db

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_initial_atom_zero_iff_below_barrier
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The initial Stieltjes atom is strictly positive exactly above the barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (ω : Ω) :
    0 < dividendMeasure (barrierStrategy X x a) ω ({0} : Set ℝ) ↔
      a < x := by
  have hiff :=
    barrierStrategy_initial_atom_zero_iff_below_barrier X x a hx ha ω
  constructor
  · intro hpos
    by_contra hax
    have hz := hiff.mpr (le_of_not_gt hax)
    exact (ne_of_gt hpos) hz
  · intro hax
    have hn :
        dividendMeasure (barrierStrategy X x a) ω ({0} : Set ℝ) ≠ 0 := by
      intro hz
      exact (not_le_of_gt hax) (hiff.mp hz)
    exact lt_of_le_of_ne bot_le hn.symm
