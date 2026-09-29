-- Prove2me | solution 1 for BookProof.ChapterParityMajoranaQuant.iJ_herm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:17:30.49204+00:00
-- url     : https://prove2.me/submissions/2c23640f-7cc5-4e9e-8d65-8c59e2429c2a

-- Generated from ChapterParityMajoranaQuant.lean — solution of BookProof.ChapterParityMajoranaQuant.iJ_herm
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant











open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

set_option maxHeartbeats 1000000 in
theorem solution (hskew : Jᴴ = -J) : (iJ J)ᴴ = iJ J := by

  unfold iJ
  rw [conjTranspose_smul, hskew, Complex.star_def, Complex.conj_I, smul_neg, neg_smul, neg_neg]
