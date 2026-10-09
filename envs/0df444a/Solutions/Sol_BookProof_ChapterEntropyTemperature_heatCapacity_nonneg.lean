-- Prove2me | solution 1 for BookProof.ChapterEntropyTemperature.heatCapacity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T10:40:47.517713+00:00
-- url     : https://prove2.me/submissions/d783c81c-e94c-4404-967b-fb74082d594b

import Mathlib
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterEntropyTemperature

open BookProof.ChapterEntropyTemperature BookProof.ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxSharpness

theorem solution {m : ℕ} (beta : ℝ) (s : Fin m → ℝ) : 0 ≤ heatCapacity beta s := by
  unfold heatCapacity varScore
  refine mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun l _ => mul_nonneg ?_ (sq_nonneg _))
  unfold scoreSoftmax
  exact div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun k _ => (Real.exp_pos _).le)
