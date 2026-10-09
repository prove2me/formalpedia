-- Prove2me | solution 1 for BookProof.ChapterElectroweakFieldStrength.eps_swap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:33:10.193318+00:00
-- url     : https://prove2.me/submissions/dfeeb7f3-5e23-43a7-802e-3573a5b32e7c

-- Generated from ChapterElectroweakFieldStrength.lean — solution of BookProof.ChapterElectroweakFieldStrength.eps_swap
import Mathlib
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterElectroweakFieldStrength



open Matrix


open BookProof.ChapterParity BookProof.ChapterParitySU2

set_option maxHeartbeats 1000000 in
theorem solution (a b c : Fin 3) : eps a b c = -eps b a c := by

  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [eps]
