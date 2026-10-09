-- Prove2me | solution 1 for BookProof.ChapterF6.mgT_cons
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:04:49.274181+00:00
-- url     : https://prove2.me/submissions/e12976e9-f575-4325-8db9-e1065f696d45

-- Generated from ChapterF6.lean — solution of BookProof.ChapterF6.mgT_cons
import Mathlib
import Definitions.Def_ChapterF6
open BookProof.ChapterF6



open scoped BigOperators


variable {α : Type*} [DecidableEq α]

variable {α : Type*} [DecidableEq α]

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (T : α →₀ ℕ) (x : α) (xs : List α) :
    mgT k T (x :: xs) = mgT k (mgStep k T x) xs := by

  simp [mgT, List.foldl_cons]
