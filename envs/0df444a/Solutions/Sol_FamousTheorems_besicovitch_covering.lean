-- Prove2me | solution 1 for FamousTheorems.besicovitch_covering
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T17:15:45.251619+00:00
-- url     : https://prove2.me/submissions/45768574-d6e8-487a-9b89-272550f4f091

import Mathlib

theorem solution {α : Type*} [MetricSpace α] [SecondCountableTopology α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [HasBesicovitchCovering α] (μ : MeasureTheory.Measure α) [MeasureTheory.SFinite μ]
    (f : α → Set ℝ) (s : Set α) (hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Set.Ioo 0 δ).Nonempty) (R : α → ℝ)
    (hR : ∀ x ∈ s, 0 < R x) :
    ∃ (t : Set α) (r : α → ℝ), t.Countable ∧ t ⊆ s ∧ (∀ x ∈ t, r x ∈ f x ∩ Set.Ioo 0 (R x)) ∧
      μ (s \ ⋃ x ∈ t, Metric.closedBall x (r x)) = 0 ∧ t.PairwiseDisjoint fun x => Metric.closedBall x (r x) :=
  Besicovitch.exists_disjoint_closedBall_covering_ae μ f s hf R hR
