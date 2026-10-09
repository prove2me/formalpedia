-- Prove2me | solution 1 for BookProof.ChapterA3k.chir1_chir2_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:38:27.72897+00:00
-- url     : https://prove2.me/submissions/6924403a-f1bb-4c48-9c7a-536bddd4bb03

-- Generated from ChapterA3k.lean — solution of BookProof.ChapterA3k.chir1_chir2_comm
import Mathlib
import Definitions.Def_ChapterA3k
open BookProof.ChapterA3k



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j

set_option maxHeartbeats 1000000 in
theorem solution : chir1 * chir2 = chir2 * chir1 := by

  unfold chir1 chir2;
  ext ⟨ i, j ⟩ ⟨ k, l ⟩ ; simp only [mul_apply, kroneckerMap_apply];
  erw [ Finset.sum_product ] ; erw [ Finset.sum_product ] ; ring;
  simp [ Matrix.one_apply, mul_comm ]
