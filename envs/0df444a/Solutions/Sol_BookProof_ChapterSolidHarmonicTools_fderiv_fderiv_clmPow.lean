-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonicTools.fderiv_fderiv_clmPow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:05.997742+00:00
-- url     : https://prove2.me/submissions/052b05ff-6953-4a7d-94a1-6b75ef3bbdd9

-- Generated from ChapterSolidHarmonicTools.lean — solution of BookProof.ChapterSolidHarmonicTools.fderiv_fderiv_clmPow
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_hasFDerivAt_clmPow
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools




open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (ψ : E →L[ℝ] ℂ) (k : ℕ) (x v w : E) :
    fderiv ℝ (fderiv ℝ fun y => (ψ y) ^ k) x v w
      = (k : ℂ) * ((k : ℂ) - 1) * (ψ x) ^ (k - 2) * ψ v * ψ w := by

  have hfd : (fderiv ℝ fun y : E => (ψ y) ^ k)
      = fun y => ((k : ℂ) * (ψ y) ^ (k - 1)) • (ψ : E →L[ℝ] ℂ) := by
    funext y; exact (hasFDerivAt_clmPow ψ k y).fderiv
  rw [hfd]
  have hc : HasFDerivAt (fun y : E => (k : ℂ) * (ψ y) ^ (k - 1))
      (((k : ℂ) * ((k - 1 : ℕ) : ℂ) * (ψ x) ^ (k - 1 - 1)) • (ψ : E →L[ℝ] ℂ)) x := by
    have h := (hasFDerivAt_clmPow ψ (k - 1) x).const_mul (k : ℂ)
    convert h using 1
    ext u
    simp [mul_assoc, mul_comm, mul_left_comm]
    simp only [mul_assoc, mul_smul]
  rw [(hc.smul_const (ψ : E →L[ℝ] ℂ)).fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul]
  rcases k with _ | _ | k
  · simp
  · simp
  · push_cast; ring_nf
