-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_discrete_source_coupling_singleton_measure_bounds_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T07:58:24.025875+00:00
-- url     : https://prove2.me/submissions/83d24ab4-c19a-47de-bf81-13ffdd8d3893

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K Z : Ω → ℕ) (hK : Measurable K) (hZ : Measurable Z)
    (k : ℕ) :
    P.map K {k} ≤ P.map Z {k} + P {ω | K ω ≠ Z ω} ∧
    P.map Z {k} ≤ P.map K {k} + P {ω | K ω ≠ Z ω} := by
  have hA : {ω | K ω = k} ⊆
      {ω | Z ω = k} ∪ {ω | K ω ≠ Z ω} := by
    intro ω hω
    by_cases heq : K ω = Z ω
    · exact Or.inl (heq.symm.trans hω)
    · exact Or.inr heq
  have hB : {ω | Z ω = k} ⊆
      {ω | K ω = k} ∪ {ω | K ω ≠ Z ω} := by
    intro ω hω
    by_cases heq : K ω = Z ω
    · exact Or.inl (heq.trans hω)
    · exact Or.inr heq
  have hKA : P.map K {k} = P {ω | K ω = k} := by
    rw [Measure.map_apply hK (measurableSet_singleton k)]
    congr 1
  have hZB : P.map Z {k} = P {ω | Z ω = k} := by
    rw [Measure.map_apply hZ (measurableSet_singleton k)]
    congr 1
  constructor
  · rw [hKA, hZB]
    exact (measure_mono hA).trans (measure_union_le _ _)
  · rw [hKA, hZB]
    exact (measure_mono hB).trans (measure_union_le _ _)
