-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_generic_marked_window_count_congr
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:17:47.507273+00:00
-- url     : https://prove2.me/submissions/08e72464-97a8-4ab5-babc-3bab46ec47f6

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Defs.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (S T : Set ℝ≥0) (f g : ℝ≥0 → ℝ≥0 × ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B)
    (hFTime : ∀ u, (f u).1 = u)
    (hGTime : ∀ u, (g u).1 = u)
    (hSupport : ∀ u : ℝ≥0, 0 < u → u ≤ (n : ℝ≥0) →
      (u ∈ S ↔ u ∈ T))
    (hMarks : ∀ u : ℝ≥0, 0 < u → u ≤ (n : ℝ≥0) → f u = g u) :
    ((Measure.count.restrict S).map f) (Ioc 0 (n : ℝ≥0) ×ˢ B) =
    ((Measure.count.restrict T).map g) (Ioc 0 (n : ℝ≥0) ×ˢ B) := by
  have hA : MeasurableSet (Ioc 0 (n : ℝ≥0) ×ˢ B) :=
    measurableSet_Ioc.prod hB
  rw [Measure.map_apply hf hA, Measure.map_apply hg hA,
    Measure.restrict_apply (hf hA), Measure.restrict_apply (hg hA)]
  congr 1
  ext u
  constructor
  · rintro ⟨ha, hs⟩
    have hu : 0 < u ∧ u ≤ (n : ℝ≥0) := by
      have hfst : (f u).1 ∈ Ioc 0 (n : ℝ≥0) := ha.1
      simpa only [hFTime, Set.mem_Ioc] using hfst
    refine ⟨?_, (hSupport u hu.1 hu.2).mp hs⟩
    change g u ∈ Ioc 0 (n : ℝ≥0) ×ˢ B
    rw [← hMarks u hu.1 hu.2]
    exact ha
  · rintro ⟨ha, hs⟩
    have hu : 0 < u ∧ u ≤ (n : ℝ≥0) := by
      have hfst : (g u).1 ∈ Ioc 0 (n : ℝ≥0) := ha.1
      simpa only [hGTime, Set.mem_Ioc] using hfst
    refine ⟨?_, (hSupport u hu.1 hu.2).mpr hs⟩
    change f u ∈ Ioc 0 (n : ℝ≥0) ×ˢ B
    rw [hMarks u hu.1 hu.2]
    exact ha
