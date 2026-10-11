-- Prove2me | solution 1 for BookProof.ChapterScaledDotProduct.scoreSoftmax_div
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:22:48.048304+00:00
-- url     : https://prove2.me/submissions/4c957a1d-010c-40fe-9c86-ec3217c51b33

-- Generated from ChapterScaledDotProduct.lean — solution of BookProof.ChapterScaledDotProduct.scoreSoftmax_div
import Mathlib
import Definitions.Def_ChapterScaledDotProduct
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterScaledDotProduct



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}

variable {d : ℕ}
variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta c : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta (fun l => s l / c) j = scoreSoftmax (beta / c) s j := by

  simp only [scoreSoftmax, mul_div_assoc, div_mul_eq_mul_div]
