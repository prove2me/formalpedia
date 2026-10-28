-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.fderiv_fderiv_fst_dir_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:26:13.206133+00:00
-- url     : https://prove2.me/submissions/36c7b5ce-66b2-47ca-929b-8b5231a5e13d

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_LogLaplaceGenerator

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
open scoped ContDiff
section Bridges
variable {E L : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup L]
  [NormedSpace ℝ L]
/-- The joint derivative in a first-factor direction is the partial derivative in the first factor. -/
theorem FunctionalInequalities.KLS.BKL.Localization.fderiv_fst_dir (H : E × L → ℝ) (p : E × L) (hH : DifferentiableAt ℝ H p) (u : E) :
    fderiv ℝ H p (u, 0) = fderiv ℝ (fun y => H (y, p.2)) p.1 u := by
  have h := hH.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)
  have h' : fderiv ℝ (fun y => H (y, p.2)) p.1 =
      (fderiv ℝ H p).comp (ContinuousLinearMap.inl ℝ E L) := h.fderiv
  rw [h']
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
end Bridges
section SecondBridge
variable {E L : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup L] [NormedSpace ℝ L]
/-- The joint second derivative along a first-factor direction is the `c`-Hessian of the
restriction. -/
theorem solution (H : E × L → ℝ) (hH : ContDiff ℝ 2 H) (p : E × L) (u : E) :
    fderiv ℝ (fderiv ℝ H) p (u, 0) (u, 0) =
      bilinearIteratedFDerivTwo ℝ (fun y => H (y, p.2)) p.1 u u := by
  have hH1 : ContDiff ℝ (1 + 1) H := by
    convert hH using 1; norm_num
  have hHf : ContDiff ℝ 1 (fderiv ℝ H) :=
    (contDiff_succ_iff_fderiv (𝕜 := ℝ) (f := H) (n := 1)).mp hH1 |>.2.2
  have hHfd : Differentiable ℝ (fderiv ℝ H) := hHf.differentiable_one
  have hHd : Differentiable ℝ H := hH.differentiable (by norm_num)
  have hrestr : ContDiff ℝ 2 (fun y => H (y, p.2)) :=
    hH.comp (contDiff_id.prodMk contDiff_const)
  rw [FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply hrestr]
  have h1 : fderiv ℝ (fun y => fderiv ℝ H y (u, 0)) p (u, 0) =
      fderiv ℝ (fderiv ℝ H) p (u, 0) (u, 0) := by
    rw [((hHfd p).hasFDerivAt.clm_apply (hasFDerivAt_const (u, 0) p)).fderiv]
    simp
  rw [← h1]
  have h2 : (fun y => fderiv ℝ (fun y' => H (y', p.2)) y u) =
      fun y => fderiv ℝ H (y, p.2) (u, 0) := by
    funext y
    exact (FunctionalInequalities.KLS.BKL.Localization.fderiv_fst_dir H (y, p.2) (hHd _) u).symm
  rw [h2]
  have hK : DifferentiableAt ℝ (fun y => fderiv ℝ H y (u, 0)) p :=
    (hHfd p).clm_apply (differentiableAt_const _)
  exact FunctionalInequalities.KLS.BKL.Localization.fderiv_fst_dir (fun y => fderiv ℝ H y (u, 0)) p hK u
