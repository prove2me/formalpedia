-- Prove2me | solution 1 for BookProof.ChapterParityMajoranaQuant.annihProj_herm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:28:22.27875+00:00
-- url     : https://prove2.me/submissions/fbaad7aa-2c8a-45d1-9e80-fd6a8b0714f7

-- Generated from ChapterParityMajoranaQuant.lean — solution of BookProof.ChapterParityMajoranaQuant.annihProj_herm
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
import Theorems.Thm_BookProof_ChapterParityMajoranaQuant_iJ_herm
open BookProof.ChapterParityMajoranaQuant











open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

set_option maxHeartbeats 1000000 in
theorem solution (hskew : Jᴴ = -J) : (annihProj J)ᴴ = annihProj J := by

  unfold annihProj
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_one, iJ_herm J hskew,
    Complex.star_def, map_div₀, map_one, Complex.conj_ofNat]
