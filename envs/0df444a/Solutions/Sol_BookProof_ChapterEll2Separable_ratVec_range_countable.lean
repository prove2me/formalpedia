-- Prove2me | solution 1 for BookProof.ChapterEll2Separable.ratVec_range_countable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:34:06.202981+00:00
-- url     : https://prove2.me/submissions/6ebc9298-7dfb-454c-9a82-bb3c011cd760

-- Generated from ChapterEll2Separable.lean — solution of BookProof.ChapterEll2Separable.ratVec_range_countable
import Mathlib
import Definitions.Def_ChapterEll2Separable
open BookProof.ChapterEll2Separable



open Filter Finset
open scoped ENNReal


open BookProof.ChapterRieszFischer

set_option maxHeartbeats 1000000 in
theorem solution : (Set.range ratVec).Countable := Set.countable_range _
