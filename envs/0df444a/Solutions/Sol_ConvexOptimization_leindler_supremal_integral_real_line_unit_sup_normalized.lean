-- Prove2me | solution 1 for ConvexOptimization.leindler_supremal_integral_real_line_unit_sup_normalized
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-15T06:34:29.522693+00:00
-- url     : https://prove2.me/submissions/25bb0a24-b9ca-462c-a0ce-89cc28617e11

import Theorems.Thm_ConvexOptimization_leindler_supremal_integral_real_line_unit_sup_normalized_additive

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

private theorem lintegral_lt_top_of_compactSupport_of_le_one
    (f : ℝ → ℝ≥0∞) (hfc : HasCompactSupport f)
    (hf1 : ∀ x, f x ≤ 1) :
    (∫⁻ x, f x) < ∞ := by
  calc
    (∫⁻ x, f x) ≤
        ∫⁻ x, (tsupport f).indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ tsupport f
      · simpa [hx] using hf1 x
      · simp [hx, image_eq_zero_of_notMem_tsupport hx]
    _ ≤ volume (tsupport f) := lintegral_indicator_one_le _
    _ < ∞ := hfc.measure_lt_top

private theorem ennreal_weighted_geom_le_arith
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) :
    a ^ (1 - l) * b ^ l ≤
      ENNReal.ofReal (1 - l) * a + ENNReal.ofReal l * b := by
  have hwl : 0 ≤ 1 - l := (sub_pos.mpr hl1).le
  have hwr : 0 ≤ l := hl0.le
  have hw_sum : Real.toNNReal (1 - l) + Real.toNNReal l = 1 := by
    apply NNReal.eq
    simp [hwl, hwr]
  have hnn := NNReal.geom_mean_le_arith_mean2_weighted
    (Real.toNNReal (1 - l)) (Real.toNNReal l) a.toNNReal b.toNNReal hw_sum
  rw [← ENNReal.coe_le_coe] at hnn
  simpa [ENNReal.coe_rpow_of_nonneg, hwl, hwr,
    ENNReal.coe_toNNReal ha, ENNReal.coe_toNNReal hb,
    ENNReal.ofReal] using hnn

theorem solution
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfsup : sSup (Set.range f) = 1)
    (hgsup : sSup (Set.range g) = 1) :
    (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤
      ∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
        (1 - l) • x + l • y = z ∧
          q = f x ^ (1 - l) * g y ^ l} := by
  have hf_top : (∫⁻ x, f x) ≠ ∞ :=
    (lintegral_lt_top_of_compactSupport_of_le_one f hfc hf1).ne
  have hg_top : (∫⁻ x, g x) ≠ ∞ :=
    (lintegral_lt_top_of_compactSupport_of_le_one g hgc hg1).ne
  exact (ennreal_weighted_geom_le_arith l hl0 hl1
    (∫⁻ x, f x) (∫⁻ x, g x) hf_top hg_top).trans
      (ConvexOptimization.leindler_supremal_integral_real_line_unit_sup_normalized_additive
        l hl0 hl1 f g hf hg hfc hgc hf1 hg1 hfsup hgsup)
