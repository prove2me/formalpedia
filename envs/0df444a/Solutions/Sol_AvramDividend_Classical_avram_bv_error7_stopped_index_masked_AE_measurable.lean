-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_stopped_index_masked_AE_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:03:39.489125+00:00
-- url     : https://prove2.me/submissions/46338c23-fc86-4674-b36b-73242ba39582

import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped BigOperators

/-- A measurable stopped prefix of an a.e.-strongly-measurable finite-cell
family remains a.e.-strongly measurable, even though its length is random. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (N : ℕ) (k : Ω → ℕ) (hk : Measurable k)
    (f : ℕ → Ω → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) P) :
    AEStronglyMeasurable (fun ω =>
      ∑ i ∈ Finset.range N, if i < k ω then f i ω else 0) P := by
  have hmask (i : ℕ) : AEStronglyMeasurable
      (fun ω => if i < k ω then f i ω else 0) P := by
    have hs : MeasurableSet {ω | i < k ω} :=
      measurableSet_lt measurable_const hk
    have heq : ({ω | i < k ω}.indicator (f i)) =
        (fun ω => if i < k ω then f i ω else 0) := by
      funext ω
      by_cases h : i < k ω
      · simp [Set.indicator, h]
      · simp [Set.indicator, h]
    rw [← heq]
    exact (hf i).indicator hs
  have hsum : AEStronglyMeasurable
      (∑ i ∈ Finset.range N, fun ω =>
        if i < k ω then f i ω else 0) P := by
    apply Finset.aestronglyMeasurable_sum
    intro i hi
    exact hmask i
  have hsumEq : (fun ω =>
      ∑ i ∈ Finset.range N, if i < k ω then f i ω else 0) =
      (∑ i ∈ Finset.range N, fun ω =>
        if i < k ω then f i ω else 0) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [hsumEq]
  exact hsum
