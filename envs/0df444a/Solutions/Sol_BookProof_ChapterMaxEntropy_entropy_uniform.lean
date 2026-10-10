-- Prove2me | solution 1 for BookProof.ChapterMaxEntropy.entropy_uniform
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:19:59.765237+00:00
-- url     : https://prove2.me/submissions/0ac27d81-199c-4771-ad93-3cac98f247e7

import Mathlib
import Definitions.Def_ChapterMaxEntropy
open BookProof.ChapterMaxEntropy
open Real BigOperators Finset

variable {α : Type*} [Fintype α]

theorem solution [Nonempty α] : entropy (uniform α) = Real.log (Fintype.card α) := by
  simp only [entropy, uniform, Real.negMulLog, Real.log_inv, neg_mul, mul_neg, neg_neg]
  rw [sum_const, card_univ, nsmul_eq_mul]
  have hn : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hn]
