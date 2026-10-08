-- Prove2me | solution 1 for AvramDividend.Classical.excursion_real_tail_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:09:39.274049+00:00
-- url     : https://prove2.me/submissions/9974257c-164f-4b6a-a611-ae7fc987a2b4

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Positive measure upper tails decrease as their lower endpoint rises. -/
theorem solution
    (μ : Measure ℝ)
    (hfin : ∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) :
    AntitoneOn (fun x : ℝ => μ.real (Ici x)) (Ioi (0 : ℝ)) := by
  intro a ha b hb hab
  have hleft : 0 < a := ha
  have hmeasure : μ (Ici b) ≤ μ (Ici a) :=
    measure_mono (Ici_subset_Ici.mpr hab)
  exact ENNReal.toReal_mono (hfin a hleft) hmeasure
