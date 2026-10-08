-- Prove2me | solution 1 for AvramDividend.Classical.continuous_zero_of_ae_zero_open_positive_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:08:56.088986+00:00
-- url     : https://prove2.me/submissions/797319dd-3476-4dd4-b814-709e6ef3b9be

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [μ.IsOpenPosMeasure]
    (f : α → ℝ) (hf : Continuous f)
    (hzero : ∀ᵐ x ∂μ, f x = 0) :
    ∀ x : α, f x = 0 := by
  have hclosed : IsClosed {x : α | f x = 0} :=
    isClosed_eq hf continuous_const
  have hsupp :
      μ.support ⊆ {x : α | f x = 0} :=
    μ.support_subset_of_isClosed hclosed hzero
  intro x
  exact hsupp (by simpa [Measure.support_eq_univ])
