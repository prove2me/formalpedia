-- Prove2me | solution 1 for BookProof.ChapterA3.detExpPath_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:09:05.866229+00:00
-- url     : https://prove2.me/submissions/6bad411f-6d47-4086-844f-6b69fdaf7daf

-- Generated from ChapterA3f.lean — solution of BookProof.ChapterA3.detExpPath_add
import Mathlib
import Definitions.Def_ChapterA3f
open BookProof.ChapterA3



open Matrix NormedSpace
open scoped Norms.Operator


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (A : Matrix (Fin n) (Fin n) ℝ) (s t : ℝ) :
    detExpPath A (s + t) = detExpPath A s * detExpPath A t := by

  have h_comm : Commute (s • A) (t • A) := by
    exact Commute.smul_left ( Commute.smul_right ( Commute.refl _ ) _ ) _;
  convert congr_arg Matrix.det ( NormedSpace.exp_add_of_commute h_comm ) using 1;
  · unfold detExpPath; norm_num [ add_smul ]; rfl
  · unfold detExpPath; rw [Matrix.det_mul]; rfl
