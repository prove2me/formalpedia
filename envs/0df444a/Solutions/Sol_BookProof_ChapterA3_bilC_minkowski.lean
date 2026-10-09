-- Prove2me | solution 1 for BookProof.ChapterA3.bilC_minkowski
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:34:10.685448+00:00
-- url     : https://prove2.me/submissions/db167af4-733e-45a4-beac-134a4d0db49d

-- Generated from ChapterA3h.lean — solution of BookProof.ChapterA3.bilC_minkowski
import Mathlib
import Definitions.Def_ChapterA3h
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (x : Fin 4 → ℂ) : bilC (toC minkowskiMat) x = Qc x := by

  unfold bilC Qc toC minkowskiMat; simp only [map_apply, of_apply, Fin.sum_univ_four, Fin.isValue] ;
      ring;
  unfold minkowskiR; norm_num [ Fin.ext_iff, minkowskiZ ] ; ring;
