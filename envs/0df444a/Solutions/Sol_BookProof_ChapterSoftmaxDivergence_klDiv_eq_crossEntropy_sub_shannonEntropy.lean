-- Prove2me | solution 1 for BookProof.ChapterSoftmaxDivergence.klDiv_eq_crossEntropy_sub_shannonEntropy
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:44:05.129917+00:00
-- url     : https://prove2.me/submissions/ba84cce9-f7e5-4e23-8871-cb20eefffadf

-- Generated from ChapterSoftmaxDivergence.lean — solution of BookProof.ChapterSoftmaxDivergence.klDiv_eq_crossEntropy_sub_shannonEntropy
import Mathlib
import Definitions.Def_ChapterSoftmaxDivergence
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxMaxEntropy
open BookProof.ChapterSoftmaxDivergence



open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxMaxEntropy

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution {p q : Fin m → ℝ}
    (hq0 : ∀ j, 0 < q j) :
    klDiv p q = crossEntropy p q - shannonEntropy p := by
  have hterm : ∀ j : Fin m,
      p j * Real.log (p j / q j) = -(p j * Real.log (q j)) + p j * Real.log (p j) := by
    intro j
    rcases eq_or_ne (p j) 0 with h | h
    · simp [h]
    · rw [Real.log_div h (ne_of_gt (hq0 j))]; ring
  rw [klDiv, Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib,
    crossEntropy, shannonEntropy, Finset.sum_neg_distrib]
  ring
