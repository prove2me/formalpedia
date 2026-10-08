-- Prove2me | solution 1 for AvramDividend.Classical.excursion_positive_order_region_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:59:33.48676+00:00
-- url     : https://prove2.me/submissions/7a86a9c9-4b0d-49ec-a694-a6fc8fd966a1

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Change the order of nonnegative integration in 0 < height < jump magnitude. -/
theorem solution
    (μ : Measure ℝ) [SFinite μ]
    (w g : ℝ → ℝ≥0∞) (hw : Measurable w) (hg : Measurable g) :
    (∫⁻ t : ℝ, ∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then w t * g z else 0) ∂μ ∂volume) =
    (∫⁻ z : ℝ, ∫⁻ t : ℝ,
      (if 0 < t ∧ t < z then w t * g z else 0) ∂volume ∂μ) := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun t z =>
    if 0 < t ∧ t < z then w t * g z else 0
  have hset : MeasurableSet
      {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} := by
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)
  have hF : Measurable (fun p : ℝ × ℝ => F p.1 p.2) := by
    dsimp [F]
    exact (hw.comp measurable_fst).mul
      (hg.comp measurable_snd) |>.ite hset measurable_const
  have hswap : (∫⁻ t : ℝ, ∫⁻ z : ℝ, F t z ∂μ ∂volume) =
      (∫⁻ z : ℝ, ∫⁻ t : ℝ, F t z ∂volume ∂μ) :=
    MeasureTheory.lintegral_lintegral_swap hF.aemeasurable
  exact hswap
