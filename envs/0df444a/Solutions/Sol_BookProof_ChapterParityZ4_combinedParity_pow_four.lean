-- Prove2me | solution 1 for BookProof.ChapterParityZ4.combinedParity_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:12:23.741762+00:00
-- url     : https://prove2.me/submissions/cbed727d-2989-407e-8869-ab5632ed7763

-- Generated from ChapterParityZ4.lean — solution of BookProof.ChapterParityZ4.combinedParity_pow_four
import Mathlib
import Definitions.Def_ChapterParityZ4
import Theorems.Thm_BookProof_ChapterParityZ4_combinedParity_sq
import Definitions.Def_ChapterParity
import Definitions.Def_ChapterParityQL
import Definitions.Def_ChapterA3
open BookProof.ChapterParityZ4



open Matrix


open BookProof.ChapterParity
open BookProof.ChapterParityQL
open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : combinedParity ^ 4 = 1 := by

  simp [ pow_succ' ];
  simp [ ← mul_assoc, ← pow_two, combinedParity_sq ]
