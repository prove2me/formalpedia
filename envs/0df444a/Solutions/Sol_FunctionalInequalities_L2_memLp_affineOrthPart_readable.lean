-- Prove2me | solution 1 for FunctionalInequalities.L2.memLp_affineOrthPart_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:41:49.349633+00:00
-- url     : https://prove2.me/submissions/26fe5928-55d4-445c-b886-e2279485fe7a

import Definitions.Def_KLSModular_FunctionalInequalities_L2_AffineDecomposition

open MeasureTheory
open scoped RealInnerProductSpace
section AffineOrthPart
variable {n : ℕ}
/-- The affine-orthogonal part is in `L²`. -/
theorem solution (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) :
    MemLp (FunctionalInequalities.L2.affineOrthPart μ g) 2 μ := by
    have hlin (u : EuclideanSpace ℝ (Fin n)) :
        MemLp (fun x => ⟪u, x⟫) 2 μ := by
      simpa [Function.comp_def] using
        (innerSL ℝ u).comp_memLp' hμ2
    let a : Fin n → ℝ := fun j =>
      ∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ
    have hsum :
        MemLp
          (fun x =>
            ∑ j : Fin n, a j *
              ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) 2 μ := by
      have hs :=
        memLp_finsetSum' Finset.univ (fun j _ =>
          (hlin (EuclideanSpace.basisFun (Fin n) ℝ j)).const_mul (a j))
      convert hs using 1
      funext x
      simp
    have hconst :
        MemLp (fun _ : EuclideanSpace ℝ (Fin n) => ∫ y, g y ∂μ) 2 μ :=
      memLp_const _
    have hmem := (hg.sub hconst).sub hsum
    convert hmem using 1
    funext x
    simp [FunctionalInequalities.L2.affineOrthPart, a]
