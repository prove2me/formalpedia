-- Prove2me | solution 1 for BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_max
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:43:45.701837+00:00
-- url     : https://prove2.me/submissions/f1eabf21-a18a-4fe3-af36-f6cee24875b7

-- Generated from ChapterSoftmaxSharpness.lean — solution of BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_max
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
import Theorems.Thm_BookProof_ChapterSoftmaxSharpness_scoreSoftmax_eq_inv_sum
import Theorems.Thm_BookProof_ChapterSoftmaxSharpness_tendsto_scoreSoftmax_denom
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness



open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (s : Fin m → ℝ) (j : Fin m)
    (hmax : ∀ l, l ≠ j → s l < s j) :
    Tendsto (fun b : ℝ => scoreSoftmax b s j) atTop (𝓝 1) := by

  have h := (tendsto_scoreSoftmax_denom s j hmax).inv₀ (by norm_num)
  simpa [scoreSoftmax_eq_inv_sum, one_div] using h
