-- Prove2me | solution 2 for BookProof.ChapterAttentionMasking.maskedSoftmax_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T10:25:21.143981+00:00
-- url     : https://prove2.me/submissions/476194db-4c78-4974-ad5f-f0c71b219279

import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterAttentionMasking

open BookProof.ChapterAttentionMasking

theorem solution {m : ℕ} (beta : ℝ) (s : Fin m → ℝ) (S : Finset (Fin m)) (j : Fin m) :
    0 ≤ maskedSoftmax beta s S j := by
  unfold maskedSoftmax
  split_ifs
  · exact div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun l _ => (Real.exp_pos _).le)
  · exact le_refl 0
