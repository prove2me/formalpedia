-- Prove2me | solution 1 for BookProof.ChapterParityHypercharge.mgamma5_real
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:13:04.719046+00:00
-- url     : https://prove2.me/submissions/daf1f1cb-2db9-40d4-b562-549e087bf71c

-- Generated from ChapterParityHypercharge.lean — solution of BookProof.ChapterParityHypercharge.mgamma5_real
import Mathlib
import Definitions.Def_ChapterParityHypercharge
import Definitions.Def_ChapterA3
open BookProof.ChapterParityHypercharge



open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : (mgamma5).map (starRingEnd ℂ) = mgamma5 := by

  ext i j; simp [mgamma5]
