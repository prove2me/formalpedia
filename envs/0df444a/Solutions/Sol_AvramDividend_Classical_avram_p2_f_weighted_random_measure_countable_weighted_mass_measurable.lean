-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_random_measure_countable_weighted_mass_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:45:36.000675+00:00
-- url     : https://prove2.me/submissions/33e1a886-ad66-4e44-a34f-70dc0810ab97

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Exact countable marked-cell masses are measurable in the sample when
each original mass kernel and its weight is measurable. -/
theorem solution
    {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [Countable ι]
    (M : Ω → Measure α) (C : ι → Set α)
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i, Measurable (H i))
    (hMass : ∀ i, Measurable (fun ω => M ω (C i))) :
    Measurable (fun ω => ∑' i, H i ω * M ω (C i)) := by
  exact Measurable.ennreal_tsum
    (fun i => (hH i).mul (hMass i))
