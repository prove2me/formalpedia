-- Prove2me | solution 1 for BookProof.ChapterPinDoubleCover.LamZ_neg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:59:56.732646+00:00
-- url     : https://prove2.me/submissions/6ea70712-b3d7-4b57-8417-b340351b4d04

-- Generated from ChapterPinDoubleCover.lean — solution of BookProof.ChapterPinDoubleCover.LamZ_neg
import Mathlib
import Definitions.Def_ChapterPinDoubleCover
import Definitions.Def_ChapterA3
open BookProof.ChapterPinDoubleCover



open Matrix


open BookProof.ChapterA3
open Classical

set_option maxHeartbeats 1000000 in
theorem solution : ∀ S ∈ Omega, LamZ S = LamZ (-S) := by
 decide
