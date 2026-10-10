-- Prove2me | solution 1 for BookProof.ChapterParityChirality.QLProj_trace
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:49.551966+00:00
-- url     : https://prove2.me/submissions/edabbc0c-4167-4f76-88e3-40b687a88ea3

-- Generated from ChapterParityChirality.lean — solution of BookProof.ChapterParityChirality.QLProj_trace
import Mathlib
import Definitions.Def_ChapterParityChirality
import Theorems.Thm_BookProof_ChapterParityChirality_chi_trace
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterParity
import Definitions.Def_ChapterParitySU2
open BookProof.ChapterParityChirality



open Matrix
open scoped Kronecker


open BookProof.ChapterA3
open BookProof.ChapterParity
open BookProof.ChapterParitySU2

set_option maxHeartbeats 1000000 in
theorem solution : QLProj.trace = 4 := by

  unfold QLProj;
  norm_num [ Matrix.trace_sub, chi_trace ]
