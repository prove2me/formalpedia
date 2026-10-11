-- Prove2me | solution 1 for BookProof.NavierStokesFlow.Carleman.linearFullData_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:07:34.436295+00:00
-- url     : https://prove2.me/submissions/72eb10ce-c498-4138-888a-0290eb327efa

-- Generated from ChapterNavierStokesCarleman.lean — solution of BookProof.NavierStokesFlow.Carleman.linearFullData_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman



open scoped ENNReal



open LpNat DiagonalEsa FullEsa

set_option maxHeartbeats 1000000 in
theorem solution : linearFullData = halfLineFullData linearMode 1 := rfl
