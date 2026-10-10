-- Prove2me | solution 1 for BookProof.ChapterParityChirality.igamma5_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:41.58164+00:00
-- url     : https://prove2.me/submissions/e24bdbcd-bebd-4753-8bca-66e30d88acfa

-- Generated from ChapterParityChirality.lean — solution of BookProof.ChapterParityChirality.igamma5_sq
import Mathlib
import Definitions.Def_ChapterParityChirality
import Theorems.Thm_BookProof_ChapterA3_mgamma5_sq
import Definitions.Def_ChapterParity
import Definitions.Def_ChapterParitySU2
import Definitions.Def_ChapterA3
open BookProof.ChapterParityChirality



open Matrix
open scoped Kronecker


open BookProof.ChapterA3
open BookProof.ChapterParity
open BookProof.ChapterParitySU2

set_option maxHeartbeats 1000000 in
theorem solution : igamma5 * igamma5 = -1 := by

  unfold igamma5;
  convert congr_arg ( fun x => kroneckerMap ( fun x1 x2 => x1 * x2 ) ( 1 : Matrix ( Fin 2 ) ( Fin 2
      ) ℂ ) x ) BookProof.ChapterA3.mgamma5_sq using 1;
  · ext i j;
    simp only [kroneckerMap, mul_apply, of_apply];
    simp only [one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite,
        Finset.sum_const_zero, add_zero];
    split_ifs <;> simp_all only [Finset.sum_filter, ↓reduceIte, ite_self, Finset.sum_const_zero];
    rw [ ← Finset.sum_filter ];
    refine Finset.sum_bij ( fun x hx => x.2 ) ?_ ?_ ?_ ?_ <;> aesop;
  · ext i j ; fin_cases i <;> fin_cases j <;> norm_num
