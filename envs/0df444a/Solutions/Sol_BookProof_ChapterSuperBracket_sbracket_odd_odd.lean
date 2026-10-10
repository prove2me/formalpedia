-- Prove2me | solution 1 for BookProof.ChapterSuperBracket.sbracket_odd_odd
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:13:23.159951+00:00
-- url     : https://prove2.me/submissions/2c8689e8-ff51-43d0-955b-eb70c8b27634

-- Generated from ChapterSuperBracket.lean — solution of BookProof.ChapterSuperBracket.sbracket_odd_odd
import Mathlib
import Definitions.Def_ChapterSuperBracket
open BookProof.ChapterSuperBracket




variable {R : Type*} [Ring R]

variable {R : Type*} [Ring R]


@[simp] private theorem eps_true_true : eps true true = -1 := rfl

set_option maxHeartbeats 1000000 in
theorem solution (a b : R) : sbracket true true a b = a * b + b * a := by

  simp only [sbracket, eps_true_true]
  push_cast
  noncomm_ring
