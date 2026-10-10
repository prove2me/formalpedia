-- Prove2me | solution 1 for BookProof.ChapterMajoranaFourier.majoranaFourier_boostBlock_unitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:44:05.401806+00:00
-- url     : https://prove2.me/submissions/71910ff3-e502-4b71-9716-884a40e57202

-- Generated from ChapterMajoranaFourier.lean — solution of BookProof.ChapterMajoranaFourier.majoranaFourier_boostBlock_unitary
import Mathlib
import Definitions.Def_ChapterMajoranaFourier
import Theorems.Thm_BookProof_ChapterMajoranaFourier_boost_sq_add
import Theorems.Thm_BookProof_ChapterMajoranaFourier_Aop_conjTranspose
import Theorems.Thm_BookProof_ChapterMajoranaFourier_Aop_sq
import Theorems.Thm_BookProof_ChapterMajoranaFourier_boostBlock_unitary
import Definitions.Def_ChapterA3
open BookProof.ChapterMajoranaFourier



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution
    (m q : ℝ) (hm : 0 ≤ m) (hq : 0 < q)
    (n : Fin 3 → ℝ) (hn : ∑ i, (n i) ^ 2 = 1) :
    (boostBlock (boostC m q) (boostS m q) (Aop n))ᴴ *
      boostBlock (boostC m q) (boostS m q) (Aop n) = 1 := boostBlock_unitary (Aop_conjTranspose n) (Aop_sq n hn) (boost_sq_add m q hm hq)
