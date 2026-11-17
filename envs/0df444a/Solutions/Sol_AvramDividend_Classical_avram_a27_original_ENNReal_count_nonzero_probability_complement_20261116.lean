-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_ENNReal_count_nonzero_probability_complement_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:44:24.630647+00:00
-- url     : https://prove2.me/submissions/9c748801-bf97-4684-98c7-48870244f407

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Ω → ℝ≥0∞) (hC : Measurable C) :
    (P {ω : Ω | C ω ≠ 0}).toReal =
      1 - (P {ω : Ω | C ω = 0}).toReal := by
  have hm : MeasurableSet {ω : Ω | C ω = 0} :=
    hC (measurableSet_singleton (0 : ℝ≥0∞))
  have hcom : P {ω : Ω | C ω ≠ 0} = 1 - P {ω : Ω | C ω = 0} := by
    simpa only [measure_univ, Set.compl_setOf] using
      (measure_compl hm (measure_ne_top P _))
  have hle : P {ω : Ω | C ω = 0} ≤ 1 := by
    calc
      P {ω : Ω | C ω = 0} ≤ P Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  rw [hcom, ENNReal.toReal_sub_of_le]
  · simp
  · exact hle
  · simp
