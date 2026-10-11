-- Prove2me | solution 1 for BookProof.ChapterScaledDotProduct.flipEquiv_apply_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:22:26.607238+00:00
-- url     : https://prove2.me/submissions/437026fd-3bf2-459b-a341-34dddd2d66e5

-- Generated from ChapterScaledDotProduct.lean — solution of BookProof.ChapterScaledDotProduct.flipEquiv_apply_self
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
theorem solution (i : Fin d) (x : Fin d → Bool) :
    (flipEquiv i x) i = !(x i) := by

  simp [flipEquiv, flipAt]
