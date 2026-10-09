-- Prove2me | solution 1 for BookProof.ChapterElectroweakFieldStrength.eps_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:32:57.154391+00:00
-- url     : https://prove2.me/submissions/3bff88bb-e834-4e02-b78b-2d7027ac5a6e

-- Generated from ChapterElectroweakFieldStrength.lean — solution of BookProof.ChapterElectroweakFieldStrength.eps_cyclic
import Mathlib
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterElectroweakFieldStrength



open Matrix


open BookProof.ChapterParity BookProof.ChapterParitySU2

set_option maxHeartbeats 1000000 in
theorem solution (a b c : Fin 3) : eps a b c = eps c a b := by

  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [eps]
