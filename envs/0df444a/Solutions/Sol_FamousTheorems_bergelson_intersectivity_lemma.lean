-- Prove2me | solution 1 for FamousTheorems.bergelson_intersectivity_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:49:31.142823+00:00
-- url     : https://prove2.me/submissions/a134f167-bb01-4f72-b28a-7fde17ba6d75

import Mathlib

theorem solution {ι α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {r : ENNReal} [Infinite ι] {s : ι → Set α} (hs : ∀ i, MeasurableSet (s i)) (hr₀ : r ≠ 0)
    (hr : ∀ i, r ≤ μ (s i)) :
    ∃ t : Set ι, t.Infinite ∧ ∀ ⦃u : Set ι⦄, u ⊆ t → u.Finite → 0 < μ (⋂ i ∈ u, s i) :=
  bergelson hs hr₀ hr
