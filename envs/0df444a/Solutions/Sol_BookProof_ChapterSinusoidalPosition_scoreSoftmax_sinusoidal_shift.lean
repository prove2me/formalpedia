-- Prove2me | solution 1 for BookProof.ChapterSinusoidalPosition.scoreSoftmax_sinusoidal_shift
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:54:00.148282+00:00
-- url     : https://prove2.me/submissions/fa793c2f-22a9-4f01-bd30-91e6d2b6b57b

-- Generated from ChapterSinusoidalPosition.lean — solution of BookProof.ChapterSinusoidalPosition.scoreSoftmax_sinusoidal_shift
import Mathlib
import Definitions.Def_ChapterSinusoidalPosition
import Theorems.Thm_BookProof_ChapterSinusoidalPosition_peInner_shift
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSinusoidalPosition



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} (beta : ℝ) (w : Fin n → ℝ) (p t : ℝ)
    (k : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta (fun l => peInner w (p + t) (k l + t)) j
      = scoreSoftmax beta (fun l => peInner w p (k l)) j := by

  congr 1
  funext l
  exact peInner_shift w p (k l) t
