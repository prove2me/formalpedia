-- Prove2me | solution 1 for BookProof.ChapterGravitySplit.minkForm_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:31:21.277267+00:00
-- url     : https://prove2.me/submissions/f38e15ca-c702-481f-9186-cfa98716c615

-- Generated from ChapterGravitySplit.lean — solution of BookProof.ChapterGravitySplit.minkForm_self
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
theorem solution (x : Fin 4 → ℝ) : minkForm x x = minkSq x := by

  rfl
