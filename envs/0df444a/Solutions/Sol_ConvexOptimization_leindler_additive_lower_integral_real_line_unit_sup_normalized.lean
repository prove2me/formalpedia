-- Prove2me | solution 1 for ConvexOptimization.leindler_additive_lower_integral_real_line_unit_sup_normalized
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-15T07:53:55.622803+00:00
-- url     : https://prove2.me/submissions/c058dd9f-9405-4190-90f8-9e9be2859796

import Theorems.Thm_ConvexOptimization_weighted_unit_grid_sum_le_supremal_envelope_lintegral
import Theorems.Thm_ConvexOptimization_weighted_unit_lintegral_eq_iSup_grid

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem solution
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfsup : sSup (Set.range f) = 1)
    (hgsup : sSup (Set.range g) = 1)
    (hmajor : ∀ x y : ℝ,
      f x ^ (1 - l) * g y ^ l ≤ h ((1 - l) • x + l • y)) :
    ENNReal.ofReal (1 - l) * (∫⁻ x, f x) +
        ENNReal.ofReal l * (∫⁻ x, g x) ≤
      ∫⁻ z, h z := by
  rw [ConvexOptimization.weighted_unit_lintegral_eq_iSup_grid
    l hl0 hl1 f g hf hg hf1 hg1]
  apply iSup_le
  intro N
  refine (ConvexOptimization.weighted_unit_grid_sum_le_supremal_envelope_lintegral
    N.1 N.2 l hl0 hl1 f g hf hg hfc hgc hf1 hg1 hfsup hgsup).trans ?_
  apply lintegral_mono
  intro z
  apply sSup_le
  intro q hq
  rcases hq with ⟨x, y, hxy, rfl⟩
  rw [← hxy]
  exact hmajor x y
