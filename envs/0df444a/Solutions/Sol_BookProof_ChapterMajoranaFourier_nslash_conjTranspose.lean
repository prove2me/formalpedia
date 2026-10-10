-- Prove2me | solution 1 for BookProof.ChapterMajoranaFourier.nslash_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:42:35.541129+00:00
-- url     : https://prove2.me/submissions/903f1568-af3e-4574-a074-c3beb1b969f2

-- Generated from ChapterMajoranaFourier.lean — solution of BookProof.ChapterMajoranaFourier.nslash_conjTranspose
import Mathlib
import Definitions.Def_ChapterMajoranaFourier
import Theorems.Thm_BookProof_ChapterMajoranaFourier_dgamma_conjTranspose
import Definitions.Def_ChapterA3
open BookProof.ChapterMajoranaFourier



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (n : Fin 3 → ℝ) : (nslash n)ᴴ = -nslash n := by

  unfold nslash; simp only [Complex.coe_smul, conjTranspose_sum, conjTranspose_smul, star_trivial] ;
  rw [ ← Finset.sum_neg_distrib ] ; congr ; ext i ; rw [ dgamma_conjTranspose ] ; aesop;
