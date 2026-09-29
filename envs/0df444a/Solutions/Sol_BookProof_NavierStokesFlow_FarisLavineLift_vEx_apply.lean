-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.vEx_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T21:51:22.171002+00:00
-- url     : https://prove2.me/submissions/a1eabb76-17e0-4a2a-8b28-210bb817c498

-- Generated from ChapterNavierStokesFarisLavineLift.lean - theorem BookProof.NavierStokesFlow.FarisLavineLift.vEx_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift

theorem solution (i : Fin 2) : vEx i = 1 := by
  fin_cases i <;> simp [vEx]
