-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_eq_zero_of_notMem_tsupport_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:51:23.370245+00:00
-- url     : https://prove2.me/submissions/7b79fe2f-9be1-43db-9857-836c05dd7e76

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- **The weighted Laplacian is local**: it vanishes at every point outside the closed support of
its argument, because both the gradient and the second derivative do. The potential is
unrestricted. -/
theorem solution (U : E → ℝ) {f : E → ℝ} {x : E}
    (hx : x ∉ tsupport f) : FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x = 0 := by
  have h1 : fderiv ℝ f x = 0 := by
    by_contra h
    exact hx (support_fderiv_subset (𝕜 := ℝ) h)
  have h2 : fderiv ℝ (fderiv ℝ f) x = 0 := by
    by_contra h
    exact hx (tsupport_fderiv_subset (𝕜 := ℝ) (support_fderiv_subset (𝕜 := ℝ) h))
  have hgrad : gradient f x = 0 := by
    rw [gradient, h1, map_zero]
  have hlap : Laplacian.laplacian f x = 0 := by
    rw [FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_sum_fderiv_fderiv, h2]
    simp
  rw [FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_apply, hlap, hgrad, inner_zero_right, sub_zero]
