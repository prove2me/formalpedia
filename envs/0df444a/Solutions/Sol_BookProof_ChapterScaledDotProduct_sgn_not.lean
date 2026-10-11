-- Prove2me | solution 1 for BookProof.ChapterScaledDotProduct.sgn_not
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:21:35.44872+00:00
-- url     : https://prove2.me/submissions/57152f75-b5df-46c8-a402-a8f48c2b36f9

-- Generated from ChapterScaledDotProduct.lean — solution of BookProof.ChapterScaledDotProduct.sgn_not
import Mathlib
import Definitions.Def_ChapterScaledDotProduct
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterScaledDotProduct



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b : Bool) : sgn (!b) = -sgn b := by

  cases b <;> simp [sgn]
