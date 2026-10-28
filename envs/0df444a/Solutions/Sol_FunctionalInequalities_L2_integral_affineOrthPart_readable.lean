-- Prove2me | solution 1 for FunctionalInequalities.L2.integral_affineOrthPart_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:41:38.917259+00:00
-- url     : https://prove2.me/submissions/f9274176-09de-40ad-8bf8-de8944458db0

import Definitions.Def_KLSModular_FunctionalInequalities_L2_AffineDecomposition

open MeasureTheory
open scoped RealInnerProductSpace
section AffineOrthPart
variable {n : ℕ}
/-- The affine-orthogonal part is centered. -/
theorem solution (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0) {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : MemLp g 2 μ) :
    ∫ x, FunctionalInequalities.L2.affineOrthPart μ g x ∂μ = 0 := by
    have hlin (u : EuclideanSpace ℝ (Fin n)) :
        MemLp (fun x : EuclideanSpace ℝ (Fin n) => ⟪u, x⟫) 2 μ := by
      simpa [Function.comp_def] using
        ((innerSL ℝ u).comp_memLp' hμ2)

    have hmean (u : EuclideanSpace ℝ (Fin n)) :
        ∫ x, ⟪u, x⟫ ∂μ = 0 := by
      have h :=
        (innerSL ℝ u).integral_comp_comm (hμ2.integrable one_le_two)
      simpa [Function.comp_def, hμ0] using h

    have hconst (c : ℝ) : ∫ x, c ∂μ = c := by
      rw [integral_const]
      simp

    have hterm (j : Fin n) :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
              ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) μ := by
      simpa only [smul_eq_mul] using
        (((hlin (EuclideanSpace.basisFun (Fin n) ℝ j)).integrable one_le_two).const_mul
          (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ))

    have hsum :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ∑ j, (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
              ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) μ := by
      refine integrable_finsetSum Finset.univ ?_
      intro j hj
      exact hterm j

    have hsub :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            g x - ∫ y, g y ∂μ) μ := by
      exact (hg.integrable one_le_two).sub (integrable_const _)

    have hsum_zero :
        ∫ x, (∑ j, (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
          ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) ∂μ = 0 := by
      rw [integral_finsetSum]
      · apply Finset.sum_eq_zero
        intro j hj
        simp [integral_const_mul, hmean]
      · intro j hj
        exact hterm j

    unfold FunctionalInequalities.L2.affineOrthPart
    rw [integral_sub hsub hsum,
      integral_sub (hg.integrable one_le_two) (integrable_const _)]
    rw [hsum_zero]
    simp [hconst]
