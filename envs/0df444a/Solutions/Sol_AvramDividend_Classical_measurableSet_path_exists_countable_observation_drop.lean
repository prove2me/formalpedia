-- Prove2me | solution 1 for AvramDividend.Classical.measurableSet_path_exists_countable_observation_drop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T19:01:35.35266+00:00
-- url     : https://prove2.me/submissions/b949159a-0067-49db-86e2-cbff9b536781

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {ι : Type*} [Countable ι]
    (u v : ι → ℝ≥0) (r : ℝ) :
    MeasurableSet {f : (ℝ≥0 → ℝ) | ∃ i : ι, r < f (u i) - f (v i)} := by
  have hm : ∀ i : ι,
      Measurable (fun f : (ℝ≥0 → ℝ) => f (u i) - f (v i)) :=
    fun i => (measurable_pi_apply (u i)).sub (measurable_pi_apply (v i))
  have hU : MeasurableSet
      (⋃ i : ι, {f : (ℝ≥0 → ℝ) | r < f (u i) - f (v i)}) :=
    MeasurableSet.iUnion
      (fun i => measurableSet_lt measurable_const (hm i))
  simpa only [Set.iUnion_setOf] using hU