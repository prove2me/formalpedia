-- Prove2me | solution 1 for BookProof.ChapterEll2Separable.ell2_separable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:34:32.489078+00:00
-- url     : https://prove2.me/submissions/ef513200-b12c-4d64-8163-48465f7772e9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterEll2Separable.lean — solution of BookProof.ChapterEll2Separable.ell2_separable
import Mathlib
import Definitions.Def_ChapterEll2Separable
import Theorems.Thm_BookProof_ChapterEll2Separable_ratVec_range_countable
import Theorems.Thm_BookProof_ChapterEll2Separable_ratVec_dense
open BookProof.ChapterEll2Separable



open Filter Finset
open scoped ENNReal


open BookProof.ChapterRieszFischer

set_option maxHeartbeats 1000000 in
theorem solution : TopologicalSpace.SeparableSpace Ell2 := ⟨⟨Set.range ratVec, ratVec_range_countable, ratVec_dense⟩⟩
