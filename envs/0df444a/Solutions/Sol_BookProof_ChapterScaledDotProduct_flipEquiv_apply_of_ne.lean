-- Prove2me | solution 1 for BookProof.ChapterScaledDotProduct.flipEquiv_apply_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:22:27.51179+00:00
-- url     : https://prove2.me/submissions/c453c917-8c5b-4b42-9478-f29d3916871d

-- Generated from ChapterScaledDotProduct.lean — solution of BookProof.ChapterScaledDotProduct.flipEquiv_apply_of_ne
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
theorem solution {i j : Fin d} (h : j ≠ i) (x : Fin d → Bool) :
    (flipEquiv i x) j = x j := by

  simp [flipEquiv, flipAt, Function.update_of_ne h]
