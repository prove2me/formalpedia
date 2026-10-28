-- Prove2me | solution 1 for BitcoinPow.nextWork_off_boundary
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:36:57.543877+00:00
-- url     : https://prove2.me/submissions/dc75fd4b-4843-45b5-9114-2944f9fdf089

import Definitions.Def_BitcoinPow

open BitcoinPow

theorem solution (lastHeight : Nat) (lastBits : BitVec 32) (lastTime firstTime : Int)
    (h : (lastHeight + 1) % BitcoinPow.difficultyAdjustmentInterval ≠ 0) :
    BitcoinPow.nextWorkRequired lastHeight lastBits lastTime firstTime = lastBits ∧
    BitcoinPow.permittedTransition (lastHeight + 1) lastBits lastBits = true := by
  constructor
  · unfold nextWorkRequired; rw [if_pos h]
  · unfold permittedTransition; rw [if_neg h]; simp
