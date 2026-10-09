-- Prove2me | solution 1 for BookProof.FockDegreesOfFreedom.NavierStokes.card_symPair
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:12:53.843643+00:00
-- url     : https://prove2.me/submissions/b7bc6763-5534-4f5b-ab39-bf543916bbe0

-- Generated from ChapterFockDegreesOfFreedom.lean — solution of BookProof.FockDegreesOfFreedom.NavierStokes.card_symPair
import Mathlib
import Definitions.Def_ChapterFockDegreesOfFreedom
open BookProof.FockDegreesOfFreedom
open BookProof.FockDegreesOfFreedom.NavierStokes




open Fintype

set_option maxHeartbeats 1000000 in
theorem solution : Fintype.card SymPair = 6 := by
 decide
