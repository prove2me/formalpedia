-- Prove2me | solution 1 for BookProof.ChapterSinusoidalPosition.peInner_shift
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:53:56.197044+00:00
-- url     : https://prove2.me/submissions/5a5ba757-8988-498a-8663-b50cf417fc8d

-- Generated from ChapterSinusoidalPosition.lean — solution of BookProof.ChapterSinusoidalPosition.peInner_shift
import Mathlib
import Definitions.Def_ChapterSinusoidalPosition
import Theorems.Thm_BookProof_ChapterSinusoidalPosition_peInner_eq_sum_cos
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
open BookProof.ChapterSinusoidalPosition



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (w : Fin n → ℝ) (p q t : ℝ) :
    peInner w (p + t) (q + t) = peInner w p q := by

  rw [peInner_eq_sum_cos, peInner_eq_sum_cos]
  exact Finset.sum_congr rfl fun a _ => by ring_nf
