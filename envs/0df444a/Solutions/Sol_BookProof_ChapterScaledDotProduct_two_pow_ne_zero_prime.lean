-- Prove2me | solution 1 for BookProof.ChapterScaledDotProduct.two_pow_ne_zero_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:34:30.787607+00:00
-- url     : https://prove2.me/submissions/5db1e81b-4901-4ce6-8672-2313ba49d00a

-- Generated from ChapterScaledDotProduct.lean — solution of BookProof.ChapterScaledDotProduct.two_pow_ne_zero'
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
theorem solution : (2 : ℝ) ^ d ≠ 0 := by
 positivity
