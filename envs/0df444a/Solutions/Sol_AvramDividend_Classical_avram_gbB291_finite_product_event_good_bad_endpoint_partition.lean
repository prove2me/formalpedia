-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB291_finite_product_event_good_bad_endpoint_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:15:30.449381+00:00
-- url     : https://prove2.me/submissions/a1c3eacb-184e-4bb9-9e13-bd62892f2c2a

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- A time event covered by finitely many good cells, a bad event, and null endpoints has mass at most the component bounds. -/
theorem solution
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (S E B : Set α) (G : ℕ → Set α) (N : ℕ)
    (hcover : S ⊆ E ∪ (B ∪ ⋃ i ∈ Finset.range N, G i))
    (hE : μ E = 0) :
    μ S ≤ μ B + ∑ i ∈ Finset.range N, μ (G i) := by
  have hBU : μ (B ∪ ⋃ i ∈ Finset.range N, G i) ≤
      μ B + μ (⋃ i ∈ Finset.range N, G i) :=
    measure_union_le B _
  have hU : μ (⋃ i ∈ Finset.range N, G i) ≤
      ∑ i ∈ Finset.range N, μ (G i) :=
    measure_biUnion_finset_le (Finset.range N) G
  have hEU : μ (E ∪ (B ∪ ⋃ i ∈ Finset.range N, G i)) ≤
      μ E + μ (B ∪ ⋃ i ∈ Finset.range N, G i) :=
    measure_union_le E _
  calc
    μ S ≤ μ (E ∪ (B ∪ ⋃ i ∈ Finset.range N, G i)) :=
      measure_mono hcover
    _ ≤ μ E + μ (B ∪ ⋃ i ∈ Finset.range N, G i) := hEU
    _ ≤ μ E + (μ B + μ (⋃ i ∈ Finset.range N, G i)) :=
      add_le_add_right hBU (μ E)
    _ ≤ μ E + (μ B + ∑ i ∈ Finset.range N, μ (G i)) :=
      add_le_add_right (add_le_add_right hU (μ B)) (μ E)
    _ = _ := by simp [hE]
