-- Prove2me | solution 1 for FunctionalInequalities.L2.integral_affineOrthPart_mul_sub_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:42:48.516504+00:00
-- url     : https://prove2.me/submissions/ca4d9514-bc0b-4c7f-b725-62e53d922a39

import Definitions.Def_KLSModular_FunctionalInequalities_L2_AffineDecomposition
import Theorems.Thm_FunctionalInequalities_L2_integral_affineOrthPart_readable
import Theorems.Thm_FunctionalInequalities_L2_integral_inner_mul_affineOrthPart_readable
import Theorems.Thm_FunctionalInequalities_L2_memLp_affineOrthPart_readable

open MeasureTheory
open scoped RealInnerProductSpace
section AffineOrthPart
variable {n : ℕ}
/-- **The affine-orthogonal part is orthogonal to the affine part**: `∫ g̃ (g - g̃) = 0`. -/
theorem solution (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) :
    ∫ x, FunctionalInequalities.L2.affineOrthPart μ g x * (g x - FunctionalInequalities.L2.affineOrthPart μ g x) ∂μ = 0 := by
    have hp : MemLp (FunctionalInequalities.L2.affineOrthPart μ g) 2 μ :=
      FunctionalInequalities.L2.memLp_affineOrthPart_readable μ hμ2 hg
    have hp_int : Integrable (FunctionalInequalities.L2.affineOrthPart μ g) μ :=
      hp.integrable one_le_two
    have hinner (j : Fin n) :
        MemLp
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) 2 μ := by
      change
        MemLp
          (fun x : EuclideanSpace ℝ (Fin n) =>
            (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)) x) 2 μ
      simpa [Function.comp_def, id] using
        ((innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).comp_memLp' hμ2)
    have hterm (j : Fin n) :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ *
              FunctionalInequalities.L2.affineOrthPart μ g x) μ := by
      change
        Integrable
          ((fun x : EuclideanSpace ℝ (Fin n) =>
              ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) *
            FunctionalInequalities.L2.affineOrthPart μ g) μ
      exact (hinner j).integrable_mul hp
    have hsum :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ∑ j : Fin n,
              (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                (⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ *
                  FunctionalInequalities.L2.affineOrthPart μ g x)) μ := by
      exact integrable_finsetSum _ fun j _ =>
        (hterm j).const_mul
          (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ)
    have hsum_int :
        (∫ x, ∑ j : Fin n,
            (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
              (⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ *
                FunctionalInequalities.L2.affineOrthPart μ g x) ∂μ) =
          ∑ j : Fin n, ∫ x,
            (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
              (⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ *
                FunctionalInequalities.L2.affineOrthPart μ g x) ∂μ := by
      apply integral_finsetSum
      intro j hj
      exact (hterm j).const_mul
        (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ)
    have hpoint (x : EuclideanSpace ℝ (Fin n)) :
        FunctionalInequalities.L2.affineOrthPart μ g x * (g x - FunctionalInequalities.L2.affineOrthPart μ g x) =
          (∫ y, g y ∂μ) * FunctionalInequalities.L2.affineOrthPart μ g x +
            ∑ j : Fin n,
              (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                (⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ *
                  FunctionalInequalities.L2.affineOrthPart μ g x) := by
      simp only [FunctionalInequalities.L2.affineOrthPart]
      rw [show
        g x -
            (g x - ∫ y, g y ∂μ -
              ∑ j : Fin n,
                (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) =
          (∫ y, g y ∂μ) +
            ∑ j : Fin n,
              (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ by ring]
      rw [mul_add, Finset.mul_sum]
      ring_nf
    have hconst :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            (∫ y, g y ∂μ) * FunctionalInequalities.L2.affineOrthPart μ g x) μ :=
      hp_int.const_mul _
    calc
      ∫ x, FunctionalInequalities.L2.affineOrthPart μ g x * (g x - FunctionalInequalities.L2.affineOrthPart μ g x) ∂μ =
          ∫ x,
            (∫ y, g y ∂μ) * FunctionalInequalities.L2.affineOrthPart μ g x +
              ∑ j : Fin n,
                (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  (⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ *
                    FunctionalInequalities.L2.affineOrthPart μ g x) ∂μ := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ =
          (∫ y, g y ∂μ) * (∫ x, FunctionalInequalities.L2.affineOrthPart μ g x ∂μ) +
            ∑ j : Fin n,
              (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                (∫ x,
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ *
                    FunctionalInequalities.L2.affineOrthPart μ g x ∂μ) := by
        rw [integral_add hconst hsum, integral_const_mul, hsum_int]
        simp only [integral_const_mul]
      _ = 0 := by
        rw [FunctionalInequalities.L2.integral_affineOrthPart_readable μ hμ2 hμ0 hg]
        simp_rw [
          FunctionalInequalities.L2.integral_inner_mul_affineOrthPart_readable μ hμ2 hμ0 hμcov hg]
        simp
