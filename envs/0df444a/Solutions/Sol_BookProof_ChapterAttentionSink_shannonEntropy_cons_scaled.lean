-- Prove2me | solution 1 for BookProof.ChapterAttentionSink.shannonEntropy_cons_scaled
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:40:15.651519+00:00
-- url     : https://prove2.me/submissions/ff26e612-955b-4083-aebd-5b90525f4497

-- Generated from ChapterAttentionSink.lean — solution of BookProof.ChapterAttentionSink.shannonEntropy_cons_scaled
import Mathlib
import Definitions.Def_ChapterAttentionSink
import Definitions.Def_ChapterAttentionEntropy
open BookProof.ChapterAttentionEntropy
open BookProof.ChapterAttentionSink



open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {w : ℝ} (hw1 : w < 1) {p : Fin m → ℝ}
    (hp : ∀ j, 0 < p j) (hsum : ∑ j, p j = 1) :
    shannonEntropy (Fin.cons w (fun j => (1 - w) * p j) : Fin (m + 1) → ℝ)
      = (-w * Real.log w - (1 - w) * Real.log (1 - w)) + (1 - w) * shannonEntropy p := by

  have hw1' : 0 < 1 - w := by linarith
  have hterm : ∀ j : Fin m,
      ((1 - w) * p j) * Real.log ((1 - w) * p j)
        = (1 - w) * Real.log (1 - w) * p j + (1 - w) * (p j * Real.log (p j)) := by
    intro j
    rw [Real.log_mul hw1'.ne' (hp j).ne']
    ring
  rw [shannonEntropy, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hsum, mul_one, shannonEntropy]
  ring
