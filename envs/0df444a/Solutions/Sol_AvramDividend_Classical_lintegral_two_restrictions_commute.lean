-- Prove2me | solution 1 for AvramDividend.Classical.lintegral_two_restrictions_commute
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T15:17:06.034875+00:00
-- url     : https://prove2.me/submissions/702f6461-4534-469d-a902-f578640f7c5b

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
    (s t : Set α)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (f : α → ℝ≥0∞) :
    (∫⁻ x in s, if x ∈ t then f x else 0 ∂μ) =
    (∫⁻ x, if x ∈ s then f x else 0 ∂(μ.restrict t)) := by
  classical
  change (∫⁻ x, t.indicator f x ∂(μ.restrict s)) =
    (∫⁻ x, s.indicator f x ∂(μ.restrict t))
  rw [lintegral_indicator ht, lintegral_indicator hs]
  change (∫⁻ x, f x ∂((μ.restrict s).restrict t)) =
    (∫⁻ x, f x ∂((μ.restrict t).restrict s))
  rw [Measure.restrict_restrict ht, Measure.restrict_restrict hs]
  rw [Set.inter_comm s t]
