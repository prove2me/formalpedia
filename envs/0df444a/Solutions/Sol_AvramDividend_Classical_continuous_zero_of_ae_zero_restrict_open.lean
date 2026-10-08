-- Prove2me | solution 1 for AvramDividend.Classical.continuous_zero_of_ae_zero_restrict_open
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:27:47.742504+00:00
-- url     : https://prove2.me/submissions/e2c42c96-f8bf-4d20-9fac-d77fb423624e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem solution
    (μ : Measure ℝ) [μ.IsOpenPosMeasure]
    (f : ℝ → ℝ) (hf : Continuous f)
    (s : Set ℝ) (hs : IsOpen s)
    (hae : ∀ᵐ x ∂(μ.restrict s), f x = 0) :
    ∀ x ∈ s, f x = 0 := by
  have hc : IsClosed {x : ℝ | f x = 0} :=
    isClosed_eq hf continuous_const
  have hsupp :
      (μ.restrict s).support ⊆ {x : ℝ | f x = 0} :=
    (μ.restrict s).support_subset_of_isClosed hc hae
  intro x hx
  have hxs : x ∈ (μ.restrict s).support := by
    apply Measure.interior_inter_support
    exact ⟨by simpa [hs.interior_eq] using hx, by simpa [Measure.support_eq_univ]⟩
  exact hsupp hxs
