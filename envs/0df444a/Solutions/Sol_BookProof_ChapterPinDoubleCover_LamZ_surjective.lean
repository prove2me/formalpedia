-- Prove2me | solution 1 for BookProof.ChapterPinDoubleCover.LamZ_surjective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:59:54.328415+00:00
-- url     : https://prove2.me/submissions/7012511f-9dc7-4387-8b86-b9dc46a784a6

-- Generated from ChapterPinDoubleCover.lean — solution of BookProof.ChapterPinDoubleCover.LamZ_surjective
import Mathlib
import Definitions.Def_ChapterPinDoubleCover
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterLorentzGroup
open BookProof.ChapterPinDoubleCover



open Matrix


open BookProof.ChapterA3
open Classical

set_option maxHeartbeats 1000000 in
theorem solution : Delta = Omega.image LamZ := by
 decide
