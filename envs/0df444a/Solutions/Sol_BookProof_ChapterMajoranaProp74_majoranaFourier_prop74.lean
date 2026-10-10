-- Prove2me | solution 1 for BookProof.ChapterMajoranaProp74.majoranaFourier_prop74
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:46:49.021154+00:00
-- url     : https://prove2.me/submissions/e5d4d8c0-791c-467a-bf7c-76eca1a4b82b

-- Generated from ChapterMajoranaProp74.lean — solution of BookProof.ChapterMajoranaProp74.majoranaFourier_prop74
import Mathlib
import Definitions.Def_ChapterMajoranaProp74
import Theorems.Thm_BookProof_ChapterMajoranaProp74_prop74_intertwine
import Theorems.Thm_BookProof_ChapterMajoranaFourier_Ep_pos
import Theorems.Thm_BookProof_ChapterMajoranaFourier_boost_sq_add
import Theorems.Thm_BookProof_ChapterMajoranaFourier_boost_sq_sub
import Theorems.Thm_BookProof_ChapterMajoranaFourier_boost_two_mul
import Theorems.Thm_BookProof_ChapterMajoranaFourier_gamma0_nslash_anticomm
import Theorems.Thm_BookProof_ChapterMajoranaFourier_gamma0_sq
import Theorems.Thm_BookProof_ChapterMajoranaFourier_nslash_sq
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterMajoranaFourier
open BookProof.ChapterMajoranaProp74



open Matrix


open BookProof.ChapterMajoranaFourier
open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (m q : ℝ) (hm : 0 ≤ m) (hq : 0 < q)
    (n : Fin 3 → ℝ) (hn : ∑ i, (n i) ^ 2 = 1) :
    Qmat (dgamma 0) (nslash n) m q * Sinv (Aop n) (boostC m q) (boostS m q)
      = Sinv (Aop n) (boostC m q) (boostS m q) * Rmat (dgamma 0) (Ep m q) := by

        convert prop74_intertwine ( dgamma 0 ) ( nslash n ) gamma0_sq ( nslash_sq n hn ) (
            gamma0_nslash_anticomm n ) ( boostC m q ) ( boostS m q ) m q ( Ep m q ) ( boost_sq_add m
                q hm hq ) _ _ using 1
        · rfl
        · rfl
        · rw [ boost_sq_sub m q hm hq, div_mul_cancel₀ _ ( ne_of_gt ( Ep_pos m q hq ) ) ]
        · rw [ BookProof.ChapterMajoranaFourier.boost_two_mul m q hm hq, div_mul_cancel₀ _ (
            ne_of_gt ( BookProof.ChapterMajoranaFourier.Ep_pos m q hq ) ) ]
