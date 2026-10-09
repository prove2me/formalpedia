-- Prove2me | solution 1 for BookProof.ChapterAttentionMarkov.l1dist_push_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:04:58.705683+00:00
-- url     : https://prove2.me/submissions/e5a95aa3-c82b-4399-aa10-f881582ab674

-- Generated from ChapterAttentionMarkov.lean — solution of BookProof.ChapterAttentionMarkov.l1dist_push_le
import Mathlib
import Definitions.Def_ChapterAttentionMarkov
open BookProof.ChapterAttentionMarkov



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {P : Fin m → Fin m → ℝ} (hP : IsStochastic P) (p q : Fin m → ℝ) :
    l1dist (push P p) (push P q) ≤ l1dist p q := by

  have hstep : ∀ j : Fin m, |push P p j - push P q j| ≤ ∑ i, |p i - q i| * P i j := by
    intro j
    have hdiff : push P p j - push P q j = ∑ i, (p i - q i) * P i j := by
      simp only [push, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hdiff]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => by
      rw [abs_mul, abs_of_nonneg (hP.1 i j)]
  calc l1dist (push P p) (push P q) ≤ ∑ j, ∑ i, |p i - q i| * P i j :=
        Finset.sum_le_sum fun j _ => hstep j
    _ = ∑ i, |p i - q i| := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum, hP.2 i, mul_one]
    _ = l1dist p q := rfl
