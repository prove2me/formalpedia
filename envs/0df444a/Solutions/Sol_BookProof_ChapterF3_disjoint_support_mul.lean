-- Prove2me | solution 1 for BookProof.ChapterF3.disjoint_support_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:59:19.902286+00:00
-- url     : https://prove2.me/submissions/a4342698-68f0-4c56-8cc6-fecc25178291

-- Generated from ChapterF3.lean — solution of BookProof.ChapterF3.disjoint_support_mul
import Mathlib
import Definitions.Def_ChapterF3
open BookProof.ChapterF3



open scoped BigOperators
open Polynomial


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {α : Type*} (f g : α → ℂ)
    (h : Disjoint (Function.support f) (Function.support g)) : f * g = 0 := by

  ext x;
  by_cases hx : f x = 0 <;> simp_all [ Function.mem_support, Set.disjoint_left ]
