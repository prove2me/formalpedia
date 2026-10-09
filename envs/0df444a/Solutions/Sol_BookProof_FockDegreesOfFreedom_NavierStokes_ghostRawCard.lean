-- Prove2me | solution 1 for BookProof.FockDegreesOfFreedom.NavierStokes.ghostRawCard
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:13:31.800467+00:00
-- url     : https://prove2.me/submissions/562ee2e6-7723-4cb1-8421-dc7d7c2a367d

-- Generated from ChapterFockDegreesOfFreedom.lean — solution of BookProof.FockDegreesOfFreedom.NavierStokes.ghostRawCard
import Mathlib
import Definitions.Def_ChapterFockDegreesOfFreedom
open BookProof.FockDegreesOfFreedom
open BookProof.FockDegreesOfFreedom.NavierStokes




open Fintype

set_option maxHeartbeats 1000000 in
theorem solution : Fintype.card GhostRaw = 3 + 1 := by
 simp
