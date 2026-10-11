-- Prove2me | solution 1 for BookProof.ChapterScaledDotProduct.card_signPatterns
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:22:25.688336+00:00
-- url     : https://prove2.me/submissions/c1c57b7b-acdc-47b9-8b86-ed34609285ea

-- Generated from ChapterScaledDotProduct.lean — solution of BookProof.ChapterScaledDotProduct.card_signPatterns
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
theorem solution : Fintype.card (Fin d → Bool) = 2 ^ d := by

  simp
