-- Prove2me | solution 1 for ConvexOptAlg.Ellipsoid.volume_scaledCopy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:43:09.8873+00:00
-- url     : https://prove2.me/submissions/15b8ca0e-77a5-452c-b741-cece4da77625

import Mathlib
import Definitions.Def_ConvexOptAlg_Ellipsoid_Defs

open MeasureTheory ConvexOptAlg.Ellipsoid in
theorem solution {n : ℕ} (X : Set (Fin n → ℝ)) (hX : IsConvexBody X)
    (f : (Fin n → ℝ) → ℝ) (hfcont : ContinuousOn f X) (hfconv : ConvexOn ℝ X f)
    (xstar : Fin n → ℝ) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    volume (scaledCopy X xstar ε) = ENNReal.ofReal (ε ^ n) * volume X := by
  have h : scaledCopy X xstar ε = AffineMap.homothety xstar ε '' X := by
    unfold scaledCopy
    congr 1
    funext x
    rw [AffineMap.homothety_apply]
    simp only [vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
    abel
  rw [h, Measure.addHaar_image_homothety, Module.finrank_fin_fun, abs_of_nonneg (pow_nonneg hε0 n)]
