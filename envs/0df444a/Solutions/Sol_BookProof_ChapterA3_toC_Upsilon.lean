-- Prove2me | solution 1 for BookProof.ChapterA3.toC_Upsilon
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:11:43.928494+00:00
-- url     : https://prove2.me/submissions/836e1252-78b4-49fc-8b49-59b4c2adedd5

-- Generated from ChapterA3h.lean — solution of BookProof.ChapterA3.toC_Upsilon
import Mathlib
import Definitions.Def_ChapterA3h
import Theorems.Thm_BookProof_ChapterA3_upsilonC_real
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ) :
    toC (Upsilon T) = UpsilonC T := by

  ext μ ν; simp only [toC, map_apply] ;
  exact Complex.conj_eq_iff_re.mp ( upsilonC_real T μ ν ) ▸ rfl
