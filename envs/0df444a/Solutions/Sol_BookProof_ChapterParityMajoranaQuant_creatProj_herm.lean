-- Prove2me | solution 1 for BookProof.ChapterParityMajoranaQuant.creatProj_herm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:26:21.550278+00:00
-- url     : https://prove2.me/submissions/e92a5317-79c6-4adc-ab8c-72cef6f7cbca

-- Generated from ChapterParityMajoranaQuant.lean — solution of BookProof.ChapterParityMajoranaQuant.creatProj_herm
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
import Theorems.Thm_BookProof_ChapterParityMajoranaQuant_iJ_herm
open BookProof.ChapterParityMajoranaQuant











open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

set_option maxHeartbeats 1000000 in
theorem solution (hskew : Jᴴ = -J) : (creatProj J)ᴴ = creatProj J := by

  unfold creatProj
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_one, iJ_herm J hskew,
    Complex.star_def, map_div₀, map_one, Complex.conj_ofNat]
