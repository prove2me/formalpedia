-- Prove2me | solution 1 for FamousTheorems.lebesgue_number_lemma_metric
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:08:39.13661+00:00
-- url     : https://prove2.me/submissions/8bb00241-860b-4905-9183-e3e38d1ede04

import Mathlib

theorem solution {α : Type*} [PseudoMetricSpace α] {s : Set α} {ι : Sort*} {c : ι → Set α} (hs : IsCompact s)
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) : ∃ δ > 0, ∀ x ∈ s, ∃ i, Metric.ball x δ ⊆ c i :=
  lebesgue_number_lemma_of_metric hs hc₁ hc₂
