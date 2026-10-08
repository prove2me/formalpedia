-- Prove2me | solution 1 for ConvexOptAlg.SmoothGD.eq_3_4
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T13:41:43.654983+00:00
-- url     : https://prove2.me/submissions/55b01ce8-2f4c-4ae6-9a8b-67e9fc931911

import Theorems.Thm_ConvexOptAlg_SmoothGD_lemma_3_4

open scoped InnerProductSpace
open ConvexOptAlg.SmoothGD

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β) (x y : EuclideanSpace ℝ (Fin n)) :
    0 ≤ f x - f y - ⟪g y, x - y⟫_ℝ ∧ f x - f y - ⟪g y, x - y⟫_ℝ ≤ β / 2 * ‖x - y‖ ^ 2 := by
  constructor
  · have hc := hconv.comp_affineMap (AffineMap.lineMap y x)
    have hd : HasDerivAt (f ∘ AffineMap.lineMap y x) ⟪g y, x - y⟫_ℝ (0 : ℝ) := by
      convert (hf.2.1 (AffineMap.lineMap y x (0 : ℝ))).hasFDerivAt.comp_hasDerivAt 0
        (AffineMap.hasDerivAt_lineMap (a := y) (b := x) (x := (0 : ℝ))) using 1 <;> first | rfl | simp
    have h := hc.le_slope_of_hasDerivAt (x := 0) (y := 1) (by simp) (by simp) (by norm_num) hd
    simp only [slope_def_field, Function.comp_apply, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one, sub_zero, div_one] at h
    linarith
  · exact (le_abs_self _).trans (lemma_3_4 f g β hf x y)
