-- Prove2me | solution 1 for BookProof.ChapterSuperBracket.eps_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:10:24.467113+00:00
-- url     : https://prove2.me/submissions/1738cfe2-71ec-414a-8ff7-0667b408535e

-- Generated from ChapterSuperBracket.lean — solution of BookProof.ChapterSuperBracket.eps_comm
import Mathlib
import Definitions.Def_ChapterSuperBracket
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterSuperBracket




variable {R : Type*} [Ring R]

variable {R : Type*} [Ring R]

set_option maxHeartbeats 1000000 in
theorem solution (p q : Bool) : eps p q = eps q p := by

  cases p <;> cases q <;> rfl
