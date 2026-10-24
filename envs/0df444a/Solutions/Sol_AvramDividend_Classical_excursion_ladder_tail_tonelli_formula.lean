-- Prove2me | solution 1 for AvramDividend.Classical.excursion_ladder_tail_tonelli_formula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T13:25:07.42862+00:00
-- url     : https://prove2.me/submissions/c6896122-a329-4f0a-a0b4-4780528fc001

import Theorems.Thm_AvramDividend_Classical_excursion_positive_order_region_tonelli
import Theorems.Thm_AvramDividend_Classical_excursion_ordered_tail_inner_lintegral
import Theorems.Thm_AvramDividend_Classical_excursion_ordered_height_inner_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- The weighted positive-jump tail has the expected truncated-height area. -/
theorem solution
    (μ : Measure ℝ) [SFinite μ]
    (w g : ℝ → ℝ≥0∞) (hw : Measurable w) (hg : Measurable g) :
    (∫⁻ t : ℝ, (Ioi (0 : ℝ)).indicator w t *
       (∫⁻ z in Ioi t, g z ∂μ) ∂volume) =
    (∫⁻ z : ℝ, g z *
       (∫⁻ t in Ioo (0 : ℝ) z, w t ∂volume) ∂μ) := by
  calc
    (∫⁻ t : ℝ, (Ioi (0 : ℝ)).indicator w t *
        (∫⁻ z in Ioi t, g z ∂μ) ∂volume) =
      (∫⁻ t : ℝ, ∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then w t * g z else 0) ∂μ ∂volume) := by
      apply lintegral_congr
      intro t
      by_cases ht : 0 < t
      · simpa [Set.indicator, ht] using
          (excursion_ordered_tail_inner_lintegral μ t ht g hg (w t)).symm
      · simp [Set.indicator, ht]
    _ = (∫⁻ z : ℝ, ∫⁻ t : ℝ,
        (if 0 < t ∧ t < z then w t * g z else 0) ∂volume ∂μ) :=
      excursion_positive_order_region_tonelli μ w g hw hg
    _ = (∫⁻ z : ℝ, g z *
        (∫⁻ t in Ioo (0 : ℝ) z, w t ∂volume) ∂μ) := by
      apply lintegral_congr
      intro z
      exact excursion_ordered_height_inner_lintegral z w hw (g z)
