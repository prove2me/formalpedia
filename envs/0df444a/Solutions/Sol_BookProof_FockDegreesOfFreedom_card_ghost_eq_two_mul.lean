-- Prove2me | solution 1 for BookProof.FockDegreesOfFreedom.card_ghost_eq_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:12:41.103047+00:00
-- url     : https://prove2.me/submissions/cbbccd50-54d0-47a7-83d5-a12a8cbf5fbd

-- Generated from ChapterFockDegreesOfFreedom.lean — solution of BookProof.FockDegreesOfFreedom.card_ghost_eq_two_mul
import Mathlib
import Definitions.Def_ChapterFockDegreesOfFreedom
open BookProof.FockDegreesOfFreedom




open Fintype

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) :
    Fintype.card (Fin (k + 1) → ZMod 2) = 2 * Fintype.card (Fin k → ZMod 2) := by

  simp [pow_succ, Nat.mul_comm]
