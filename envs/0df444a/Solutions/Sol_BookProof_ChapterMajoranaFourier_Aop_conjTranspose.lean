-- Prove2me | solution 1 for BookProof.ChapterMajoranaFourier.Aop_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:42:54.958694+00:00
-- url     : https://prove2.me/submissions/69f35407-f0da-4069-80de-c81faac57f73

-- Generated from ChapterMajoranaFourier.lean — solution of BookProof.ChapterMajoranaFourier.Aop_conjTranspose
import Mathlib
import Definitions.Def_ChapterMajoranaFourier
import Theorems.Thm_BookProof_ChapterMajoranaFourier_dgamma_conjTranspose
import Theorems.Thm_BookProof_ChapterMajoranaFourier_nslash_conjTranspose
import Theorems.Thm_BookProof_ChapterMajoranaFourier_gamma0_nslash_anticomm
import Definitions.Def_ChapterA3
open BookProof.ChapterMajoranaFourier



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (n : Fin 3 → ℝ) : (Aop n)ᴴ = Aop n := by

  unfold Aop; simp only [Fin.isValue, conjTranspose_mul] ;
  rw [ nslash_conjTranspose, dgamma_conjTranspose ] ; norm_num;
  rw [ gamma0_nslash_anticomm, neg_neg ]
