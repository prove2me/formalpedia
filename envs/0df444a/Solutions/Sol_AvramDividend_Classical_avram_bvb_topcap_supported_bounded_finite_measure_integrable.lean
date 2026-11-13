-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_topcap_supported_bounded_finite_measure_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:25:09.235065+00:00
-- url     : https://prove2.me/submissions/061f3aa3-f517-4e83-b655-23504d1f16e4

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

theorem solution
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Set α) (hS : MeasurableSet S) (hSfinite : μ S < ⊤)
    (f : α → ℝ) (hf : Measurable f)
    (hSupport : ∀ a, a ∉ S → f a = 0)
    (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ a ∈ S, |f a| ≤ K) :
    Integrable f μ := by
  have hConst : Integrable (S.indicator (fun _ : α => K)) μ := by
    haveI : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hSfinite⟩
    exact (integrable_indicator_iff hS).2 (integrable_const K)
  have hDom : ∀ᵐ a ∂μ, ‖f a‖ ≤ S.indicator (fun _ : α => K) a := by
    filter_upwards [] with a
    by_cases ha : a ∈ S
    · simpa only [Set.indicator_of_mem ha, Real.norm_eq_abs,
        abs_of_nonneg hK] using hBound a ha
    · simp [Set.indicator_of_notMem ha, hSupport a ha]
  exact hConst.mono' hf.aestronglyMeasurable hDom
