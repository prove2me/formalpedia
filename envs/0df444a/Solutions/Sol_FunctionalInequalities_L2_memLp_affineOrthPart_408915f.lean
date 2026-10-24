-- Prove2me | solution 1 for FunctionalInequalities.L2.memLp_affineOrthPart_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:44:30.493456+00:00
-- url     : https://prove2.me/submissions/0109d8bc-5f5b-411f-a453-bb6a72f42bab

import Definitions.Def_KLS408915f_FunctionalInequalities_L2_AffineDecomposition
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
section AffineOrthPart
variable {n : ℕ}
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities.L2 in
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
