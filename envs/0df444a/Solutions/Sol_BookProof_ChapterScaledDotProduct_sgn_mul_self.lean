-- Prove2me | solution 1 for BookProof.ChapterScaledDotProduct.sgn_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:44:42.263009+00:00
-- url     : https://prove2.me/submissions/78701608-57a7-45c4-896a-e0d4ce5ce3e4

-- Generated from ChapterScaledDotProduct.lean — theorem BookProof.ChapterScaledDotProduct.sgn_mul_self
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterScaledDotProduct
open BookProof.ChapterScaledDotProduct


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}
open BookProof.ChapterScaledDotProduct

theorem solution(b : Bool) : sgn b * sgn b = 1 := by
  first
  | (cases b <;> simp [sgn])
  | (cases b <;> norm_num [sgn])
