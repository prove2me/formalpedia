-- Prove2me | solution 1 for BookProof.ChapterA3.hasDerivAt_detExpPath_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:09:19.951799+00:00
-- url     : https://prove2.me/submissions/0a37c244-6038-4706-a807-448fb4836d11

-- Generated from ChapterA3f.lean — solution of BookProof.ChapterA3.hasDerivAt_detExpPath_zero
import Mathlib
import Definitions.Def_ChapterA3f
import Theorems.Thm_BookProof_ChapterA3_differentiable_det
import Theorems.Thm_BookProof_ChapterA3_hasDerivAt_det_line
open BookProof.ChapterA3



open Matrix NormedSpace
open scoped Norms.Operator


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (A : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (detExpPath A) A.trace 0 := by

  have hline : HasDerivAt (fun t : ℝ => (1 + t • A).det) A.trace 0 := hasDerivAt_det_line A
  have hf : HasFDerivAt (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ)
      (fderiv ℝ (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ)
        (1 : Matrix (Fin n) (Fin n) ℝ)) (1 : Matrix (Fin n) (Fin n) ℝ) := by
    apply_rules [DifferentiableAt.hasFDerivAt, differentiable_det]
  have hchain : HasDerivAt (fun t : ℝ => Matrix.det (1 + t • A))
      (fderiv ℝ (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ)
        (1 : Matrix (Fin n) (Fin n) ℝ) A)
      0 := by
    have hc : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin n) (Fin n) ℝ) + t • A) A 0 := by
      have h1 : HasDerivAt (fun _ : ℝ => (1 : Matrix (Fin n) (Fin n) ℝ))
          (0 : Matrix (Fin n) (Fin n) ℝ) 0 := hasDerivAt_const _ _
      have h2 : HasDerivAt (fun t : ℝ => t • A) A 0 := by
        convert (hasDerivAt_id (0 : ℝ)).smul_const A using 1 <;> (first | rfl | simp)
      convert HasDerivAt.add h1 h2 using 1 <;> (first | rfl | simp)
    have hf2 : HasFDerivAt (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ)
        (fderiv ℝ (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ)
          (1 : Matrix (Fin n) (Fin n) ℝ))
        (1 + (0 : ℝ) • A) := by
      convert hf using 1 <;> (first | rfl | simp)
    exact HasFDerivAt.comp_hasDerivAt 0 hf2 hc
  have hval : fderiv ℝ (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ)
      (1 : Matrix (Fin n) (Fin n) ℝ) A = A.trace := (hline.unique hchain).symm
  have hcurve : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A)) A 0 := by
    have h := hasDerivAt_exp_smul_const' A (0 : ℝ)
    simp only [zero_smul, exp_zero, mul_one] at h
    exact h
  have hf1 : HasFDerivAt (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ)
      (fderiv ℝ (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ)
        (1 : Matrix (Fin n) (Fin n) ℝ))
      (NormedSpace.exp ((0 : ℝ) • A)) := by
    convert hf using 1 <;> (first | rfl | simp [exp_zero])
  have hexp0 : HasDerivAt (fun u : ℝ => Matrix.det (NormedSpace.exp (u • A)))
      (fderiv ℝ (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ)
        (1 : Matrix (Fin n) (Fin n) ℝ) A) 0 :=
    HasFDerivAt.comp_hasDerivAt 0 hf1 hcurve
  have hexp : HasDerivAt (fun u : ℝ => Matrix.det (NormedSpace.exp (u • A))) A.trace 0 := by
    convert hexp0 using 1 <;> (first | rfl | simp [hval])
  exact hexp
