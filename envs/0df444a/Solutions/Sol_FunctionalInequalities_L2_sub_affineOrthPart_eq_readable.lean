-- Prove2me | solution 1 for FunctionalInequalities.L2.sub_affineOrthPart_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:47.32757+00:00
-- url     : https://prove2.me/submissions/1a909c03-9679-4356-beca-5bc2216f5c6d

import Definitions.Def_KLSModular_FunctionalInequalities_L2_AffineDecomposition

open MeasureTheory
open scoped RealInnerProductSpace
section AffineOrthPart
variable {n : ℕ}
/-- For `f` centered and orthogonal to the linear functions, `f - g̃ = (f - g)~`. -/
theorem solution (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0) (hg : MemLp g 2 μ) :
    f - FunctionalInequalities.L2.affineOrthPart μ g = FunctionalInequalities.L2.affineOrthPart μ (f - g) := by
    have hI :
        (∫ y, (f y - g y) ∂μ) =
          (∫ y, f y ∂μ) - ∫ y, g y ∂μ :=
      integral_sub (hf.integrable (by norm_num)) (hg.integrable (by norm_num))
    have hweighted (j : Fin n) :
        (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * (f y - g y) ∂μ) =
          (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * f y ∂μ) -
            ∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ := by
      have hfj :
          Integrable
            (fun y => ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * f y) μ := by
        convert
          ((innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).comp_memLp' hμ2).integrable_mul hf
            using 1
        rfl
      have hgj :
          Integrable
            (fun y => ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y) μ := by
        convert
          ((innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).comp_memLp' hμ2).integrable_mul hg
            using 1
        rfl
      calc
        (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * (f y - g y) ∂μ) =
            ∫ y,
              (⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * f y -
                ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with y
              ring
        _ = (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * f y ∂μ) -
            ∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ :=
          integral_sub hfj hgj
    have hweighted_neg (j : Fin n) :
        (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * (f y - g y) ∂μ) =
          -∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ := by
      rw [hweighted, hfx]
      ring
    funext x
    simp only [Pi.sub_apply, FunctionalInequalities.L2.affineOrthPart]
    rw [hI, hf0]
    simp_rw [hweighted_neg]
    simp only [Finset.sum_neg_distrib, neg_mul]
    ring
