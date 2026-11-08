-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_finite_coordinate_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:12:07.216229+00:00
-- url     : https://prove2.me/submissions/89ca710d-5430-47c4-afbf-d8953fedc7f1

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- A bounded-coefficient localisation event for a finite original-process
physical-grid row is measurable whenever every sampled coefficient is. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (n : ℕ) (a : Ω → ℕ → ℝ)
    (ha : ∀ i, Measurable (fun ω => a ω i)) (K : ℝ) :
    MeasurableSet {ω : Ω | ∀ i ∈ Finset.range (n + 1), abs (a ω i) ≤ K} := by
  classical
  have heq : {ω : Ω | ∀ i ∈ Finset.range (n + 1), abs (a ω i) ≤ K} =
      ⋂ i : ℕ, {ω : Ω | i ∈ Finset.range (n + 1) → abs (a ω i) ≤ K} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i ∈ Finset.range (n + 1)
  · have hset : {ω : Ω | i ∈ Finset.range (n + 1) → abs (a ω i) ≤ K} =
        {ω : Ω | abs (a ω i) ≤ K} := by
      ext ω
      simp [hi]
    rw [hset]
    exact measurableSet_le (ha i).abs measurable_const
  · have hset : {ω : Ω | i ∈ Finset.range (n + 1) → abs (a ω i) ≤ K} =
        Set.univ := by
      ext ω
      simp [hi]
    rw [hset]
    exact MeasurableSet.univ
