-- Prove2me | solution 1 for BookProof.ChapterAttentionSink.shannonEntropy_sink
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:40:56.334625+00:00
-- url     : https://prove2.me/submissions/c0a0b39e-8312-4b39-a851-acbc686c737b

import Definitions.Def_ChapterObservableExpectation
import Mathlib
import Definitions.Def_ChapterAttentionSink
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionEntropy
-- Generated from ChapterAttentionSink.lean — theorem BookProof.ChapterAttentionSink.shannonEntropy_sink
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionSink


open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionEntropy

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem solution (beta s0 : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    shannonEntropy (scoreSoftmax beta (Fin.cons s0 s))
      = (-sinkWeight beta s0 s * Real.log (sinkWeight beta s0 s)
          - (1 - sinkWeight beta s0 s) * Real.log (1 - sinkWeight beta s0 s))
        + (1 - sinkWeight beta s0 s) * shannonEntropy (scoreSoftmax beta s) := by
  set E0 := Real.exp (beta * s0) with hE0
  set S := ∑ l, Real.exp (beta * s l) with hSdef
  have hS : 0 < S := Finset.sum_pos (fun l _ => Real.exp_pos _) ⟨i, Finset.mem_univ _⟩
  have hE0p : 0 < E0 := Real.exp_pos _
  have hden : ∑ l : Fin (m + 1), Real.exp (beta * (Fin.cons s0 s : Fin (m + 1) → ℝ) l) = E0 + S := by
    rw [Fin.sum_univ_succ]; simp [hE0, hSdef]
  have hw : sinkWeight beta s0 s = E0 / (E0 + S) := by
    unfold sinkWeight scoreSoftmax; rw [hden]; simp [hE0]
  have h1w : 1 - sinkWeight beta s0 s = S / (E0 + S) := by
    rw [hw]; field_simp; ring
  have hp : ∀ j : Fin m, scoreSoftmax beta (Fin.cons s0 s) j.succ =
      (1 - sinkWeight beta s0 s) * scoreSoftmax beta s j := by
    intro j
    unfold scoreSoftmax; rw [hden, h1w]; simp only [Fin.cons_succ]
    rw [← hSdef]; field_simp
  have hq1 : ∑ j, scoreSoftmax beta s j = 1 := by
    unfold scoreSoftmax; rw [← Finset.sum_div, ← hSdef, div_self hS.ne']
  have hqpos : ∀ j, 0 < scoreSoftmax beta s j := fun j => div_pos (Real.exp_pos _) hS
  have h1wpos : 0 < 1 - sinkWeight beta s0 s := by rw [h1w]; positivity
  unfold shannonEntropy
  rw [Fin.sum_univ_succ]
  have h0 : scoreSoftmax beta (Fin.cons s0 s) 0 = sinkWeight beta s0 s := rfl
  rw [h0]
  simp_rw [hp]
  have hlog : ∀ j, Real.log ((1 - sinkWeight beta s0 s) * scoreSoftmax beta s j) =
      Real.log (1 - sinkWeight beta s0 s) + Real.log (scoreSoftmax beta s j) := fun j =>
    Real.log_mul h1wpos.ne' (hqpos j).ne'
  simp_rw [hlog, mul_add, Finset.sum_add_distrib]
  have e1 : ∑ x, (1 - sinkWeight beta s0 s) * scoreSoftmax beta s x * Real.log (1 - sinkWeight beta s0 s)
      = (1 - sinkWeight beta s0 s) * Real.log (1 - sinkWeight beta s0 s) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hq1, mul_one]
  have e2 : ∑ x, (1 - sinkWeight beta s0 s) * scoreSoftmax beta s x * Real.log (scoreSoftmax beta s x)
      = (1 - sinkWeight beta s0 s) * ∑ x, scoreSoftmax beta s x * Real.log (scoreSoftmax beta s x) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
  rw [e1, e2]
  ring
