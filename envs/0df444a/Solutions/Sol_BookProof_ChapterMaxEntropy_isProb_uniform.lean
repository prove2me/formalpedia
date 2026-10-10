-- Prove2me | solution 1 for BookProof.ChapterMaxEntropy.isProb_uniform
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T13:10:18.465892+00:00
-- url     : https://prove2.me/submissions/ad0dfe6a-e54e-4dd2-8324-50755d92fa5e

import Mathlib
import Definitions.Def_ChapterMaxEntropy
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterDutchBook
open BookProof.ChapterMaxEntropy
open Real BigOperators Finset

variable {α : Type*} [Fintype α]

theorem solution [Nonempty α] : IsProb (uniform α) := by
  refine ⟨fun i => ?_, ?_⟩
  · simp only [uniform]
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · simp only [uniform, sum_const, card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
