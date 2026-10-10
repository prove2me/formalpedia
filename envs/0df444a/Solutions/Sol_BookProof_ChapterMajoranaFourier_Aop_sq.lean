-- Prove2me | solution 1 for BookProof.ChapterMajoranaFourier.Aop_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:43:19.745766+00:00
-- url     : https://prove2.me/submissions/90fd4804-d6b6-4b72-bbf1-b52988660ba7

-- Generated from ChapterMajoranaFourier.lean — solution of BookProof.ChapterMajoranaFourier.Aop_sq
import Mathlib
import Definitions.Def_ChapterMajoranaFourier
import Theorems.Thm_BookProof_ChapterMajoranaFourier_gamma0_sq
import Theorems.Thm_BookProof_ChapterMajoranaFourier_gamma0_nslash_anticomm
import Theorems.Thm_BookProof_ChapterMajoranaFourier_nslash_sq
import Definitions.Def_ChapterA3
open BookProof.ChapterMajoranaFourier



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (n : Fin 3 → ℝ) (hn : ∑ i, (n i) ^ 2 = 1) :
    Aop n * Aop n = 1 := by

      convert congr_arg ( fun x : Matrix ( Fin 4 ) ( Fin 4 ) ℂ => ( nslash n ) * x * dgamma 0 ) (
          gamma0_nslash_anticomm n ) using 1;
      · simp only [Aop, mul_assoc];
      · simp [ ← mul_assoc, nslash_sq n hn, gamma0_sq ]
