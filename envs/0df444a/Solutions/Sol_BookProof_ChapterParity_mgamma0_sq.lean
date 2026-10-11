-- Prove2me | solution 1 for BookProof.ChapterParity.mgamma0_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:10:49.860325+00:00
-- url     : https://prove2.me/submissions/ad118136-e013-4eac-a55e-bbefaf266264

-- Generated from ChapterParity.lean — solution of BookProof.ChapterParity.mgamma0_sq
import Mathlib
import Definitions.Def_ChapterParity
import Definitions.Def_ChapterA3
open BookProof.ChapterParity



open Matrix
open scoped ComplexConjugate
open BookProof.ChapterA3

variable {n : Type*}

set_option maxHeartbeats 1000000 in

theorem solution : mgamma 0 * mgamma 0 = -1 := by
  have h : mgammaZ 0 * mgammaZ 0 = -1 := by decide
  have := congrArg (Int.castRingHom ℂ).mapMatrix h
  rwa [map_mul, map_neg, map_one, ← mgamma] at this
