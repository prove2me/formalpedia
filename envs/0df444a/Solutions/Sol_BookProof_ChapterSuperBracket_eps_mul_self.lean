-- Prove2me | solution 1 for BookProof.ChapterSuperBracket.eps_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:10:25.953031+00:00
-- url     : https://prove2.me/submissions/bba2cf77-5fb0-4513-b227-f9624845245b

-- Generated from ChapterSuperBracket.lean — solution of BookProof.ChapterSuperBracket.eps_mul_self
import Mathlib
import Definitions.Def_ChapterSuperBracket
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterSuperBracket




variable {R : Type*} [Ring R]

variable {R : Type*} [Ring R]

set_option maxHeartbeats 1000000 in
theorem solution (p q : Bool) : eps p q * eps p q = 1 := by

  cases p <;> cases q <;> rfl
