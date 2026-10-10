-- Prove2me | solution 1 for BookProof.ChapterLaplacianProduct.fderiv_fderiv_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:20:10.407259+00:00
-- url     : https://prove2.me/submissions/0f384a24-8ceb-4219-aee2-1d5144bcc1cb

-- Generated from ChapterLaplacianProduct.lean — solution of BookProof.ChapterLaplacianProduct.fderiv_fderiv_mul
import Mathlib
import Definitions.Def_ChapterLaplacianProduct
import Theorems.Thm_BookProof_ChapterLaplacianProduct_diffAt_fderiv
import Theorems.Thm_BookProof_ChapterLaplacianProduct_fderiv_mul_eventually
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct




open Filter Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ fun y : E => f y * g y) x
      = (g x) • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x)
        + ((f x) • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ f x).smulRight (fderiv ℝ g x)) := by

  have hdf : HasFDerivAt f (fderiv ℝ f x) x := (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hdg : HasFDerivAt g (fderiv ℝ g x) x := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hDf : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x := (diffAt_fderiv hf).hasFDerivAt
  have hDg : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) x) x := (diffAt_fderiv hg).hasFDerivAt
  have h12 : HasFDerivAt (fun y : E => g y • fderiv ℝ f y + f y • fderiv ℝ g y)
      ((g x) • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x)
        + ((f x) • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ f x).smulRight (fderiv ℝ g x))) x :=
    (hdg.smul hDf).add (hdf.smul hDg)
  rw [(fderiv_mul_eventually hf hg).fderiv_eq, h12.fderiv]
