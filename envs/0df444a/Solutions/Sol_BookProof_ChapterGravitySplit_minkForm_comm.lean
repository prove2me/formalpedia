-- Prove2me | solution 1 for BookProof.ChapterGravitySplit.minkForm_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:31:09.887197+00:00
-- url     : https://prove2.me/submissions/0c6b0675-8b92-4cfd-b4cd-643fbf87b4c1

-- Generated from ChapterGravitySplit.lean — solution of BookProof.ChapterGravitySplit.minkForm_comm
import Mathlib
import Definitions.Def_ChapterGravitySplit
import Definitions.Def_ChapterGravityTimeProj
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravitySplit




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj

set_option maxHeartbeats 1000000 in
theorem solution (x y : Fin 4 → ℝ) : minkForm x y = minkForm y x := by

  unfold minkForm lower metric; norm_num [ Fin.sum_univ_four ] ; ring;
  simp [ *, Matrix.mulVec ] ; ring!;
