-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_simultaneous_good_event_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:07:37.957286+00:00
-- url     : https://prove2.me/submissions/d48df136-115f-4bf7-a570-7cef875448d5

import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Theorems.Thm_AvramDividend_Classical_avram_a19_simultaneous_bad_union_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The complement of a small countable bad-event union has large probability. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Set Ω) (E : Nat → Set Ω)
    (hBs : MeasurableSet B) (hEs : ∀ k, MeasurableSet (E k))
    (hB : P B ≤ (1 / 4 : ENNReal))
    (hE : tsum (fun k : Nat => P (E k)) ≤ (1 / 8 : ENNReal)) :
    (5 / 8 : ENNReal) ≤ P ((B ∪ Set.iUnion E)ᶜ) := by
  have hbad := AvramDividend.Classical.avram_a19_simultaneous_bad_union_bound
    P B E hB hE
  have hmeas : MeasurableSet (B ∪ Set.iUnion E) :=
    hBs.union (MeasurableSet.iUnion hEs)
  have hsub : (1 : ENNReal) - (3 / 8 : ENNReal) ≤
      (1 : ENNReal) - P (B ∪ Set.iUnion E) :=
    tsub_le_tsub_left hbad 1
  have hsum : (1 : ENNReal) = (5 / 8 : ENNReal) + (3 / 8 : ENNReal) := by
    calc
      (1 : ENNReal) = (8 : ENNReal) / 8 :=
        (ENNReal.div_self (by norm_num) (by finiteness)).symm
      _ = (5 / 8 : ENNReal) + (3 / 8 : ENNReal) := by
        rw [ENNReal.div_add_div_same]
        norm_num
  have hnum : (1 : ENNReal) - (3 / 8 : ENNReal) = 5 / 8 :=
    ENNReal.sub_eq_of_eq_add (by finiteness) hsum
  have hfin : P (B ∪ Set.iUnion E) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hbad (by finiteness))
  rw [hnum] at hsub
  rw [measure_compl hmeas hfin]
  simpa only [measure_univ] using hsub
