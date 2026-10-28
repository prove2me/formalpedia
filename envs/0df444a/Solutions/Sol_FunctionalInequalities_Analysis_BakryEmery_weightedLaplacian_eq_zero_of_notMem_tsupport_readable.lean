-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_eq_zero_of_notMem_tsupport_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:28.027178+00:00
-- url     : https://prove2.me/submissions/9931be90-973c-45ca-bf57-324fe14bb27c

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Laplacian

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
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
