-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_simultaneous_bad_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:30:17.170192+00:00
-- url     : https://prove2.me/submissions/449629fe-b2e4-4c3c-afb5-a09103686306

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- Countably many bad-increment events have one small union. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Set Ω) (E : Nat → Set Ω)
    (hB : P B ≤ (1 / 4 : ENNReal))
    (hE : tsum (fun k : Nat => P (E k)) ≤ (1 / 8 : ENNReal)) :
    P (B ∪ Set.iUnion E) ≤ (3 / 8 : ENNReal) := by
  calc
    P (B ∪ Set.iUnion E) ≤ P B + P (Set.iUnion E) :=
      measure_union_le _ _
    _ ≤ (1 / 4 : ENNReal) + (1 / 8 : ENNReal) :=
      add_le_add hB ((measure_iUnion_le E).trans hE)
    _ = (3 / 8 : ENNReal) := by
      rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
      norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]
