-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_runner_f_generic_marked_window_count_any_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:28:56.170205+00:00
-- url     : https://prove2.me/submissions/e1180a85-4bea-42c5-b606-268f06220bb0

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (S U : Set ℝ≥0) (f g : ℝ≥0 → ℝ≥0 × ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hFTime : ∀ u, (f u).1 = u)
    (hGTime : ∀ u, (g u).1 = u)
    (hSupport : ∀ u : ℝ≥0, 0 < u → u ≤ T →
      (u ∈ S ↔ u ∈ U))
    (hMarks : ∀ u : ℝ≥0, 0 < u → u ≤ T → f u = g u) :
    ((Measure.count.restrict S).map f) (Ioc 0 T ×ˢ B) =
    ((Measure.count.restrict U).map g) (Ioc 0 T ×ˢ B) := by
  have hA : MeasurableSet (Ioc 0 T ×ˢ B) :=
    measurableSet_Ioc.prod hB
  rw [Measure.map_apply hf hA, Measure.map_apply hg hA,
    Measure.restrict_apply (hf hA), Measure.restrict_apply (hg hA)]
  congr 1
  ext u
  constructor
  · rintro ⟨ha, hs⟩
    have hu : 0 < u ∧ u ≤ T := by
      have hfst : (f u).1 ∈ Ioc 0 T := ha.1
      simpa only [hFTime, Set.mem_Ioc] using hfst
    refine ⟨?_, (hSupport u hu.1 hu.2).mp hs⟩
    change g u ∈ Ioc 0 T ×ˢ B
    rw [← hMarks u hu.1 hu.2]
    exact ha
  · rintro ⟨ha, hs⟩
    have hu : 0 < u ∧ u ≤ T := by
      have hfst : (g u).1 ∈ Ioc 0 T := ha.1
      simpa only [hGTime, Set.mem_Ioc] using hfst
    refine ⟨?_, (hSupport u hu.1 hu.2).mpr hs⟩
    change f u ∈ Ioc 0 T ×ˢ B
    rw [hMarks u hu.1 hu.2]
    exact ha
