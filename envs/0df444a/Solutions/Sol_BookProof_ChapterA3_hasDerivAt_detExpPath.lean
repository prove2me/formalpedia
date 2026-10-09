-- Prove2me | solution 1 for BookProof.ChapterA3.hasDerivAt_detExpPath
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:09:43.563001+00:00
-- url     : https://prove2.me/submissions/cef7d8e2-ca37-4e4f-a3e4-b13e4f733da0

-- Generated from ChapterA3f.lean — solution of BookProof.ChapterA3.hasDerivAt_detExpPath
import Mathlib
import Definitions.Def_ChapterA3f
import Theorems.Thm_BookProof_ChapterA3_detExpPath_add
import Theorems.Thm_BookProof_ChapterA3_hasDerivAt_detExpPath_zero
open BookProof.ChapterA3



open Matrix NormedSpace
open scoped Norms.Operator


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (detExpPath A) (A.trace * detExpPath A t) t := by

  have h_deriv : HasDerivAt (fun h => detExpPath A (t + h)) (A.trace * detExpPath A t) 0 := by
    have hadd : (fun h : ℝ => detExpPath A (t + h)) = fun h => detExpPath A t * detExpPath A h :=
      funext fun x => detExpPath_add A t x
    rw [hadd]
    convert HasDerivAt.const_mul (detExpPath A t) (hasDerivAt_detExpPath_zero A) using 1 <;>
      (first | rfl | ring)
  rw [ hasDerivAt_iff_tendsto_slope_zero ] at *;
  aesop
