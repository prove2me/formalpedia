-- Prove2me | solution 1 for BookProof.ChapterRieszFischer.finSupport_ne_univ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:03:45.417014+00:00
-- url     : https://prove2.me/submissions/c1bd6564-c30b-47e7-a9fe-6e3b7d7d9866

-- Generated from ChapterRieszFischer.lean — solution of BookProof.ChapterRieszFischer.finSupport_ne_univ
import Mathlib
import Definitions.Def_ChapterRieszFischer
import Theorems.Thm_BookProof_ChapterRieszFischer_geomVec_not_mem_finSupport
open BookProof.ChapterRieszFischer



open Filter
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution : FinSupport ≠ (Set.univ : Set Ell2) := by

  intro h
  exact geomVec_not_mem_finSupport (h ▸ Set.mem_univ geomVec)
