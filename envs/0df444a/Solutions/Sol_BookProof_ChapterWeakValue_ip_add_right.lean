-- Prove2me | solution 1 for BookProof.ChapterWeakValue.ip_add_right
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:08.897101+00:00
-- url     : https://prove2.me/submissions/4975443c-91a4-4f54-ba42-23074b305e9a

-- Generated from ChapterWeakValue.lean — solution of BookProof.ChapterWeakValue.ip_add_right
import Mathlib
import Definitions.Def_ChapterWeakValue
open BookProof.ChapterWeakValue



open scoped BigOperators Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (f v w : Fin n → ℂ) : ip f (v + w) = ip f v + ip f w := by

  simp [ip, mul_add, Finset.sum_add_distrib]
