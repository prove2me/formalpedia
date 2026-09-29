-- Prove2me | solution 1 for FamousTheorems.vitali_covering
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:16:48.402106+00:00
-- url     : https://prove2.me/submissions/79bf658c-4ffa-4319-a721-02eaf10a15ce

import Mathlib

theorem solution {α ι : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [SecondCountableTopology α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsLocallyFiniteMeasure μ] (s : Set α) (t : Set ι) (C : NNReal)
    (r : ι → ℝ) (c : ι → α) (B : ι → Set α) (hB : ∀ a ∈ t, B a ⊆ Metric.closedBall (c a) (r a))
    (μB : ∀ a ∈ t, μ (Metric.closedBall (c a) (3 * r a)) ≤ C * μ (B a)) (ht : ∀ a ∈ t, (interior (B a)).Nonempty)
    (h't : ∀ a ∈ t, IsClosed (B a)) (hf : ∀ x ∈ s, ∀ ε > 0, ∃ a ∈ t, r a ≤ ε ∧ c a = x) :
    ∃ u ⊆ t, u.Countable ∧ u.PairwiseDisjoint B ∧ μ (s \ ⋃ a ∈ u, B a) = 0 :=
  Vitali.exists_disjoint_covering_ae μ s t C r c B hB μB ht h't hf
