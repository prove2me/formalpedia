-- Prove2me | solution 1 for AvramDividend.Classical.lintegral_indicator_restrict_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:27:52.799545+00:00
-- url     : https://prove2.me/submissions/9dfbaefd-c70b-4677-b8b5-7ac8255068ec

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem solution
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (A B : Set α)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hsub : B ⊆ A) (f : α → ℝ≥0∞) :
    (∫⁻ x in A, if x ∈ B then f x else 0 ∂μ) =
    (∫⁻ x, if x ∈ B then f x else 0 ∂μ) := by
  classical
  have hBA : B ∩ A = B := Set.inter_eq_left.mpr hsub
  have hRestrict :
      (μ.restrict A).restrict B = μ.restrict B := by
    rw [Measure.restrict_restrict hB, hBA]
  calc
    (∫⁻ x in A, if x ∈ B then f x else 0 ∂μ) =
        ∫⁻ x, f x ∂((μ.restrict A).restrict B) := by
      change (∫⁻ x, B.indicator f x ∂(μ.restrict A)) = _
      exact lintegral_indicator hB f
    _ = ∫⁻ x, f x ∂(μ.restrict B) := by rw [hRestrict]
    _ = ∫⁻ x, if x ∈ B then f x else 0 ∂μ := by
      change (∫⁻ x, f x ∂(μ.restrict B)) =
        (∫⁻ x, B.indicator f x ∂μ)
      exact (lintegral_indicator hB f).symm
