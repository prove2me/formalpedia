-- Prove2me | solution 1 for Erdos180.projectiveDirection_nonzero_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:06:54.39458+00:00
-- url     : https://prove2.me/submissions/d0fa5e82-7a63-4a1f-8c08-97bf8b9efd74

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Push

open Erdos180
variable (K : Type*) [Field K]

theorem solution
    {x y x' y' : K}
    (hdet : x * y' - x' * y ≠ 0) :
    x' ≠ 0 ∨ y' ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨hx, hy⟩ := h
  apply hdet
  simp [hx, hy]
