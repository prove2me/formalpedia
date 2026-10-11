-- Prove2me | solution 1 for BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_eq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:33:23.862622+00:00
-- url     : https://prove2.me/submissions/7d116772-3bfb-4c12-b119-b77e307578b4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSoftmaxMaxEntropy.lean — solution of BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_eq
import Mathlib
import Definitions.Def_ChapterSoftmaxMaxEntropy
import Theorems.Thm_BookProof_ChapterSoftmaxMaxEntropy_shannonEntropy_scoreSoftmax
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxMaxEntropy



open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    -(beta * ∑ j, scoreSoftmax beta s j * s j) - shannonEntropy (scoreSoftmax beta s)
      = -logPartition beta s := by
  rw [shannonEntropy_scoreSoftmax beta s i, ← meanScore]
  ring
