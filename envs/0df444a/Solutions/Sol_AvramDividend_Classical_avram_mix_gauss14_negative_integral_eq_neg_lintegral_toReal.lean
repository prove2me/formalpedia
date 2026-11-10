-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_gauss14_negative_integral_eq_neg_lintegral_toReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T10:30:58.052977+00:00
-- url     : https://prove2.me/submissions/40c7f3f5-8398-46b9-972d-e35178307f1e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Convert a nonpositive real mark integral to the nonnegative mass of its negation. -/
theorem solution
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Set α) (hS : MeasurableSet S)
    (f : α → ℝ) (hf : Measurable f)
    (hneg : ∀ a ∈ S, f a ≤ 0) :
    (∫ a in S, f a ∂μ) =
      -((∫⁻ a in S, ENNReal.ofReal (-f a) ∂μ).toReal) := by
  have hnonneg : ∀ᵐ a ∂μ.restrict S, 0 ≤ -f a := by
    filter_upwards [ae_restrict_mem hS] with a ha
    exact neg_nonneg.mpr (hneg a ha)
  have hEq := integral_eq_lintegral_of_nonneg_ae
    hnonneg hf.neg.aestronglyMeasurable
  simpa only [integral_neg, neg_neg] using congrArg Neg.neg hEq
