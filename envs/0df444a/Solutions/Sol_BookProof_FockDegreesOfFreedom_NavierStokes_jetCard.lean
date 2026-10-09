-- Prove2me | solution 1 for BookProof.FockDegreesOfFreedom.NavierStokes.jetCard
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:12:54.771181+00:00
-- url     : https://prove2.me/submissions/1ca17fd6-e505-4a9e-99c1-0334e624077b

-- Generated from ChapterFockDegreesOfFreedom.lean — solution of BookProof.FockDegreesOfFreedom.NavierStokes.jetCard
import Mathlib
import Definitions.Def_ChapterFockDegreesOfFreedom
import Theorems.Thm_BookProof_FockDegreesOfFreedom_NavierStokes_card_symPair
open BookProof.FockDegreesOfFreedom
open BookProof.FockDegreesOfFreedom.NavierStokes




open Fintype

set_option maxHeartbeats 1000000 in
theorem solution : Fintype.card Jet = 33 := by

  simp [card_symPair]
