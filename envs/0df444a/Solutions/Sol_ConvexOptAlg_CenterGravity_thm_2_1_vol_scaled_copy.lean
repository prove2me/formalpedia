-- Prove2me | solution 1 for ConvexOptAlg.CenterGravity.thm_2_1_vol_scaled_copy
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-05T20:00:59.770006+00:00
-- url     : https://prove2.me/submissions/993cc16c-7c5f-4773-92bd-7a9acdf4d74b

import Mathlib
import Definitions.Def_ConvexOptAlg_CenterGravity_Defs

open MeasureTheory
open scoped InnerProductSpace


theorem solution {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (hX : ConvexOptAlg.CenterGravity.IsConvexBody X)
    {xstar : EuclideanSpace ℝ (Fin n)} (hxstar : xstar ∈ X) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    volume ((fun x => (1 - ε) • xstar + ε • x) '' X) = ENNReal.ofReal ε ^ n * volume X := by
  have h : (fun x : EuclideanSpace ℝ (Fin n) => (1 - ε) • xstar + ε • x) =
      AffineMap.homothety xstar ε := by
    funext x
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    module
  rw [h, Measure.addHaar_image_homothety, finrank_euclideanSpace_fin,
    abs_of_nonneg (pow_nonneg hε0 n), ENNReal.ofReal_pow hε0]
